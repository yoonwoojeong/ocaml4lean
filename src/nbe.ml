(* A checker for declaration values by normalisation by evaluation (prototype).

   Terms are evaluated into values: binders become closures (environment,
   pending universe substitution, body), applications of stuck heads become
   neutrals with a spine of lazy arguments, and a neutral caches its weak
   head normal form and its type in place.  Beta reduction is an environment
   push and unfolding a constant evaluates its body once per declaration
   under a level substitution, so no term is ever rebuilt by substitution.

   Checking is bidirectional over the export's terms: a lambda is checked
   against an expected Pi type and arguments against the domain, which is
   the typing judgement of Lean's kernel (infer, then is_def_eq) arranged so
   that types of lambdas never have to be built.  Conversion follows
   Tc.is_def_eq: quick checks, whnf_core, proof irrelevance, lazy delta
   reduction by definitional height with the same-head argument shortcut,
   Nat offsets and literal arithmetic, projections, eta, structure eta,
   string literals and unit-like types.

   Trust: [check_decl] either returns (the value has the declared type) or
   raises.  Callers treat every exception -- a kernel error, [Decline] for a
   case this prototype does not handle, a resource limit -- as "no verdict"
   and re-check the declaration with Tc, so a rejection is always Tc's.  Only
   acceptance by this module must be sound; a missing conversion rule costs
   time, never correctness. *)
open Expr
open Env

exception Decline of string
let decline s = raise (Decline s)
let fail = Tc.fail

(* ------------------------------------------------------------------ values *)
type value =
  | VSort of Level.t
  | VPi of thunk * clo                 (* domain, codomain *)
  | VLam of thunk * clo                (* domain, body *)
  | VNeu of neu
  | VNat of Z.t
  | VStr of string

and clo = { cenv : env; csub : sub; cbody : Expr.t }

and env = { vals : thunk list; eopen : bool }

(* universe substitution, identity when [ps = []]; [sid] identifies it for
   the evaluation memo *)
and sub = { sid : int; ps : Name.t list; ls : Level.t list }

and thunk = {
  mutable tv : value;                  (* [dummy] until forced *)
  mutable tenv : env;
  tsub : sub;
  tterm : Expr.t;
  topen : bool;                        (* may mention a local *)
}

and neu = {
  nid : int;
  head : head;
  rargs : thunk list;                  (* arguments, last first *)
  nargs : int;
  nopen : bool;
  mutable whnf_c : value;              (* whnf_core, [dummy] if unknown *)
  mutable whnf_f : value;              (* whnf *)
  mutable nty : value;                 (* type *)
}

and head =
  | HConst of Name.t * Level.t list
  | HLocal of local
  | HProj of Name.t * int * value

and local = { lid : int; lty : value }

let dummy = VStr "<unset>"
let empty_env = { vals = []; eopen = false }
let id_sub = { sid = 0; ps = []; ls = [] }

let vopen = function
  | VNeu n -> n.nopen
  | VPi (d, c) | VLam (d, c) -> d.topen || c.cenv.eopen
  | _ -> false

let of_value v = { tv = v; tenv = empty_env; tsub = id_sub; tterm = Tc.dontcare; topen = vopen v }

(* --------------------------------------------------------------- state *)
module KTbl = Hashtbl.Make (struct
    type t = Name.t * Level.t list
    let equal (a, la) (b, lb) =
      (a == b || Name.equal a b) && List.compare_lengths la lb = 0 && List.for_all2 ( == ) la lb
    let hash (a, la) = List.fold_left (fun h l -> Hc.mix h (Level.hash l)) (Name.hash a) la
  end)

module ETbl = Hashtbl.Make (struct
    type t = Expr.t * int
    let equal (a, i) (b, j) = a == b && i = j
    let hash (a, i) = Hc.mix (Expr.hash a) i
  end)

module PairSet = Hashtbl.Make (struct
    type t = int * int
    let equal ((a : int), (b : int)) (c, d) = a = c && b = d
    let hash (a, b) = Hc.mix (Hc.mix 0x9E3779B9 a) b   (* [mix a b] collides for nearby ids *)
  end)

type st = {
  tc : Tc.ctx;
  mutable next : int;                  (* ids of neutrals, locals, substitutions, contexts *)
  mutable fuel : int;
  mutable eager : bool;
  mutable rdepth : int;                (* nesting of whnf / conversion calls *)
  counts : int array;
  delta : value KTbl.t;                (* unfolded constant bodies *)
  ctype : value KTbl.t;                (* constant types *)
  subs : sub KTbl.t;
  evals : value ETbl.t;                (* closed terms by (term, substitution id) *)
  infers : value ETbl.t;               (* inferred types by (term, context id) *)
  success : unit PairSet.t;
  failure : unit PairSet.t;
}

let fresh_id st = st.next <- st.next + 1; st.next
(* work counters (O4L_NBE_STATS): evals, neutrals, thunks, forces, conv, quick-same hits,
   whnf, whnf_core, unfolds, type_of, infer, iota *)
let ncounters = 12
let counter_names = [| "eval"; "neutral"; "thunk"; "force"; "conv"; "same-hit"; "whnf"; "whnf_core";
                       "unfold"; "type_of"; "infer"; "iota" |]
let totals = Array.init ncounters (fun _ -> Atomic.make 0)
let stats_on = Sys.getenv_opt "O4L_NBE_STATS" <> None
let cnt (st : st) i = if stats_on then st.counts.(i) <- st.counts.(i) + 1
(* terms smaller than this are evaluated / inferred without memoisation *)
let memo_size = match Sys.getenv_opt "O4L_NBE_MEMO" with Some v -> int_of_string v | None -> 8
let depth = ref 0
let dbg = Sys.getenv_opt "O4L_NBE_DBG" <> None

(* Deep recursion is quadratic under OCaml 5 (every minor collection scans
   the whole stack) and a sign of a reduction Tc would avoid; beyond this
   depth the declaration is left to Tc.  [rdepth] is not restored when an
   exception escapes: any exception ends the declaration's check. *)
let max_depth = match Sys.getenv_opt "O4L_NBE_DEPTH" with Some v -> int_of_string v | None -> 1500

let enter st =
  st.rdepth <- st.rdepth + 1;
  if st.rdepth > max_depth then decline "recursion depth"
let leave st = st.rdepth <- st.rdepth - 1

let tick st =
  st.fuel <- st.fuel - 1;
  if st.fuel <= 0 then decline "fuel"

let mk_neu st head rargs nargs nopen =
  cnt st 1;
  VNeu { nid = fresh_id st; head; rargs; nargs; nopen; whnf_c = dummy; whnf_f = dummy; nty = dummy }

let const_val st n ls = mk_neu st (HConst (n, ls)) [] 0 false

let fresh_local st ty = mk_neu st (HLocal { lid = fresh_id st; lty = ty }) [] 0 true

let mk_sub st ps ls = match ps with [] -> id_sub | _ -> { sid = fresh_id st; ps; ls }

(* one substitution per (constant, levels), so the evaluation memo can share *)
let sub_for st n ps ls =
  match ps with
  | [] -> id_sub
  | _ ->
    match KTbl.find_opt st.subs (n, ls) with
    | Some s -> s
    | None -> let s = mk_sub st ps ls in KTbl.add st.subs (n, ls) s; s

let inst_level s l = if s.ps = [] then l else Level.instantiate s.ps s.ls l
let inst_levels s ls = if s.ps = [] then ls else List.map (inst_level s) ls

(* ------------------------------------------------------------- evaluation *)
let push env t = { vals = t :: env.vals; eopen = env.eopen || t.topen }

let rec nth_thunk l i = match l with
  | t :: r -> if i = 0 then t else nth_thunk r (i - 1)
  | [] -> fail "type checker does not support loose bound variables"

let rec eval st env sub e : value =
  match e with
  | BVar { idx; _ } -> force st (nth_thunk env.vals idx)
  | NatLit { n; _ } -> VNat n
  | StrLit { s; _ } -> VStr s
  | FVar _ -> decline "free variable"
  | _ ->
    if closed e && size e >= memo_size then begin
      let key = (e, sub.sid) in
      match ETbl.find_opt st.evals key with
      | Some v -> v
      | None -> let v = eval_node st empty_env sub e in ETbl.add st.evals key v; v
    end else eval_node st env sub e

and eval_node st env sub e =
  cnt st 0;
  match e with
  | Sort { l; _ } -> VSort (inst_level sub l)
  | Const { n; ls; _ } -> const_val st n (inst_levels sub ls)
  | App _ ->
    let f, args = get_app_args e in
    let fv = eval st env sub f in
    (match fv with
     | VNeu n ->
       (* one neutral for the whole spine *)
       let r = ref n.rargs and o = ref n.nopen in
       Array.iter (fun a -> let t = mk_thunk st env sub a in r := t :: !r; o := !o || t.topen) args;
       mk_neu st n.head !r (n.nargs + Array.length args) !o
     | _ -> Array.fold_left (fun v a -> apply st v (mk_thunk st env sub a)) fv args)
  | Lam { ty; b; _ } -> VLam (mk_thunk st env sub ty, { cenv = env; csub = sub; cbody = b })
  | Pi { ty; b; _ } -> VPi (mk_thunk st env sub ty, { cenv = env; csub = sub; cbody = b })
  | Let { v; b; _ } -> eval st (push env (mk_thunk st env sub v)) sub b
  | Proj { s; idx; e = se; _ } ->
    let sv = eval st env sub se in
    mk_neu st (HProj (s, idx, sv)) [] 0 (vopen sv)
  | BVar _ | NatLit _ | StrLit _ | FVar _ -> eval st env sub e

and mk_thunk st env sub e =
  match e with
  | BVar { idx; _ } -> nth_thunk env.vals idx
  | NatLit { n; _ } -> of_value (VNat n)
  | _ ->
    let c = closed e in
    cnt st 2;
    { tv = dummy; tenv = (if c then empty_env else env); tsub = sub; tterm = e;
      topen = (not c) && env.eopen }

and force st t =
  if t.tv != dummy then t.tv
  else begin
    cnt st 3;
    let v = eval st t.tenv t.tsub t.tterm in
    t.tv <- v; t.tenv <- empty_env; v
  end

and apply st v (a : thunk) =
  match v with
  | VLam (_, c) -> eval st (push c.cenv a) c.csub c.cbody
  | VNeu n -> mk_neu st n.head (a :: n.rargs) (n.nargs + 1) (n.nopen || a.topen)
  | _ -> decline "application of a non-function"

let inst st (c : clo) v = eval st (push c.cenv (of_value v)) c.csub c.cbody
let inst_thunk st (c : clo) t = eval st (push c.cenv t) c.csub c.cbody

let args_array n = let a = Array.of_list n.rargs in
  let len = Array.length a in
  Array.init len (fun i -> a.(len - 1 - i))

let apply_range st v (args : thunk array) lo hi =
  let r = ref v in
  for i = lo to hi - 1 do r := apply st !r args.(i) done;
  !r

(* re-apply the spine of [n] to [v] *)
let apply_spine st v n = List.fold_right (fun a v -> apply st v a) n.rargs v

let mk_app_vals st head args = mk_neu st head (List.rev args) (List.length args)
    (List.exists (fun t -> t.topen) args)

(* ---------------------------------------------------------- environment *)
let find st n = Tc.find st.tc n
let get st n = Tc.get st.tc n

let const_type st n ls =
  match KTbl.find_opt st.ctype (n, ls) with
  | Some v -> v
  | None ->
    let ci = get st n in
    if List.compare_lengths ci.lparams ls <> 0 then
      fail "incorrect number of universe levels for '%s'" (Name.to_string n);
    let v = eval st empty_env (sub_for st n ci.lparams ls) ci.ty in
    KTbl.add st.ctype (n, ls) v; v

let delta_info st v = match v with
  | VNeu { head = HConst (n, ls); _ } ->
    (match find st n with
     | Some ci when has_value ci && List.compare_lengths ls ci.lparams = 0 -> Some ci
     | _ -> None)
  | _ -> None

let delta_value st (ci : cinfo) ls =
  let n = ci.name in
  match KTbl.find_opt st.delta (n, ls) with
  | Some v -> v
  | None ->
    let body = match value ci with Some b -> b | None -> assert false in
    let v = eval st empty_env (sub_for st n ci.lparams ls) body in
    KTbl.add st.delta (n, ls) v; v

let unfold st v = match v, delta_info st v with
  | VNeu ({ head = HConst (_, ls); _ } as n), Some ci -> cnt st 8; Some (apply_spine st (delta_value st ci ls) n)
  | _ -> None

let is_const_app v name = match v with
  | VNeu { head = HConst (n, _); _ } -> n == name || Name.equal n name
  | _ -> false

let ctor_of st v = match v with
  | VNeu ({ head = HConst (n, ls); _ } as nu) ->
    (match find st n with Some { kind = Ctor cv; _ } -> Some (n, ls, cv, nu) | _ -> None)
  | _ -> None

let nat_type st = const_val st Tc.N.nat []
let string_type st = const_val st Tc.N.string []

let nat_to_ctor st z =
  if Z.equal z Z.zero then const_val st Tc.N.nat_zero []
  else apply st (const_val st Tc.N.nat_succ []) (of_value (VNat (Z.pred z)))

let string_to_ctor st s = eval st empty_env id_sub (Tc.string_lit_to_constructor s)

(* -------------------------------------------------------------- reduction *)
let rec whnf_core ?(cheap = false) st v =
  match v with
  | VNeu n ->
    if (not cheap) && n.whnf_c != dummy then n.whnf_c
    else begin
      cnt st 7;
      let r = match n.head with
        | HLocal _ -> v
        | HProj (s, i, sv) ->
          let sv' = if cheap then whnf_core ~cheap st sv else whnf st sv in
          (match proj_reduce st s i sv' with
           | Some fld -> whnf_core ~cheap st (apply_spine st fld n)
           | None -> v)
        | HConst (cn, ls) ->
          (match reduce_rec st n cn ls with
           | Some r -> whnf_core ~cheap st r
           | None -> v) in
      if not cheap then n.whnf_c <- r;
      r
    end
  | _ -> v

and proj_reduce st sname idx sv =
  let sv = match sv with VStr s -> whnf st (string_to_ctor st s) | _ -> sv in
  match ctor_of st sv with
  | Some (_, _, cv, nu) when Name.equal cv.induct sname ->
    if cv.cnparams + idx < nu.nargs then Some (force st (args_array nu).(cv.cnparams + idx)) else None
  | _ -> None

and reduce_rec st n cn ls =
  match find st cn with
  | Some ({ kind = Quot (QLift | QInd); _ } as ci) when st.tc.Tc.bi.quot_ok -> quot_reduce st ci n
  | Some ({ kind = Recursor r; _ } as ci) -> iota st ci r ls n
  | _ -> None

and quot_reduce st ci n =
  let mk_pos, arg_pos = match ci.kind with Quot QLift -> 5, 3 | _ -> 4, 3 in
  if n.nargs <= mk_pos then None else begin
    let args = args_array n in
    let mk = whnf st (force st args.(mk_pos)) in
    match mk with
    | VNeu ({ head = HConst (m, _); _ } as mn)
      when (match find st m with Some { kind = Quot QCtor; _ } -> true | _ -> false) && mn.nargs = 3 ->
      let a = List.hd mn.rargs in
      let r = apply st (force st args.(arg_pos)) a in
      Some (apply_range st r args (mk_pos + 1) n.nargs)
    | _ -> None
  end

and iota st ci r ls n =
  cnt st 11;
  let { rnparams = nparams; nmotives; nminors; rnindices = nindices; rules; k; _ } = r in
  let major_idx = nparams + nmotives + nminors + nindices in
  if major_idx >= n.nargs then None else begin
    let args = args_array n in
    let induct = Tc.major_induct st.tc ci (nparams, nmotives, nminors, nindices) in
    let major = force st args.(major_idx) in
    let major = match k, induct with
      | true, Some ind -> to_ctor_when_k st ind major nparams
      | _ -> major in
    let major = whnf st major in
    let major = match major with
      | VNat z -> nat_to_ctor st z
      | VStr s -> whnf st (string_to_ctor st s)
      | _ -> (match induct with Some ind -> to_ctor_when_structure st ind major | None -> major) in
    match major with
    | VNeu ({ head = HConst (cn, _); _ } as mn) ->
      (match List.find_opt (fun rl -> Name.equal rl.r_ctor cn) rules with
       | None -> None
       | Some rule ->
         if rule.r_nfields > mn.nargs || List.compare_lengths ls ci.lparams <> 0 then None
         else begin
           let rhs = eval st empty_env (sub_for st ci.name ci.lparams ls) rule.r_rhs in
           let rhs = apply_range st rhs args 0 (nparams + nmotives + nminors) in
           let margs = args_array mn in
           let rhs = apply_range st rhs margs (mn.nargs - rule.r_nfields) mn.nargs in
           Some (apply_range st rhs args (major_idx + 1) n.nargs)
         end)
    | _ -> None
  end

and to_ctor_when_k st induct major nparams =
  match type_of st major with
  | exception Decline _ -> major
  | ty ->
    match whnf st ty with
    | VNeu ({ head = HConst (n, ls); _ } as tn) as app_type when Name.equal n induct ->
      (match Tc.ind_info st.tc n with
       | Some { ctors = ctor :: _; _ } ->
         if tn.nargs < nparams then major else begin
           let targs = args_array tn in
           let params = Array.to_list (Array.sub targs 0 nparams) in
           let c = mk_app_vals st (HConst (ctor, ls)) params in
           match type_of st c with
           | exception Decline _ -> major
           | cty -> if conv st app_type cty then c else major
         end
       | _ -> major)
    | _ -> major

and to_ctor_when_structure st induct major =
  if not (Tc.is_non_rec_structure st.tc induct) || ctor_of st major <> None then major
  else begin
    match type_of st major with
    | exception Decline _ -> major
    | ty ->
      let ty = whnf st ty in
      match ty with
      | VNeu { head = HConst (n, _); _ } when Name.equal n induct ->
        if is_prop st ty then major else expand_eta_struct st ty major
      | _ -> major
  end

and expand_eta_struct st ty v =
  match ty with
  | VNeu ({ head = HConst (n, ls); _ } as tn) ->
    (match Tc.ind_info st.tc n with
     | Some { ctors = ctor :: _; _ } ->
       (match find st ctor with
        | Some { kind = Ctor { cnparams; nfields; _ }; _ } ->
          let targs = args_array tn in
          let np = min cnparams tn.nargs in
          let params = Array.to_list (Array.sub targs 0 np) in
          let fields = List.init nfields (fun i -> of_value (mk_neu st (HProj (n, i, v)) [] 0 (vopen v))) in
          mk_app_vals st (HConst (ctor, ls)) (params @ fields)
        | _ -> v)
     | _ -> v)
  | _ -> v

and nat_lit_ext st v = match v with
  | VNat z -> Some z
  | VNeu { head = HConst (n, []); nargs = 0; _ } when n == Tc.N.nat_zero || Name.equal n Tc.N.nat_zero -> Some Z.zero
  | _ -> None

(* As in Lean's type_checker::reduce_nat, terms with free variables (here:
   values that may mention a local) are not reduced by the Nat extension. *)
and reduce_nat st v =
  if (not st.tc.Tc.bi.nat_ok) || vopen v then None else
    match v with
    | VNeu ({ head = HConst (n, []); _ } as nu) ->
      if nu.nargs = 1 && (n == Tc.N.nat_succ || Name.equal n Tc.N.nat_succ) then
        (match nat_lit_ext st (whnf st (force st (List.hd nu.rargs))) with
         | Some z -> Some (VNat (Z.succ z))
         | None -> None)
      else if nu.nargs = 2 then begin
        let bin f = match nu.rargs with
          | b :: a :: _ ->
            (match nat_lit_ext st (whnf st (force st a)) with
             | None -> None
             | Some x ->
               match nat_lit_ext st (whnf st (force st b)) with
               | None -> None
               | Some y -> f x y)
          | _ -> None in
        let size_ok r = if Z.numbits r / 8 > Tc.max_nat_bytes then fail "Nat numeral too large" else Some (VNat r) in
        let nat r = Some (VNat r) in
        let bool b = Some (const_val st (if b then Tc.N.bool_true else Tc.N.bool_false) []) in
        let module N = Tc.N in
        if n == N.nat_add then bin (fun a b -> size_ok (Z.add a b))
        else if n == N.nat_sub then bin (fun a b -> nat (if Z.leq a b then Z.zero else Z.sub a b))
        else if n == N.nat_mul then bin (fun a b -> size_ok (Z.mul a b))
        else if n == N.nat_pow then bin (fun a b ->
            if Z.gt b (Z.of_int 0xFFFFFFFF) then fail "Nat.pow exponent too large";
            let k = Z.to_int b in
            if Z.gt a Z.one && k <> 0 && (Z.numbits a / 8 + 1) > Tc.max_nat_bytes / k then fail "Nat.pow result too large";
            nat (Z.pow a k))
        else if n == N.nat_gcd then bin (fun a b -> nat (Z.gcd a b))
        else if n == N.nat_mod then bin (fun a b -> nat (if Z.equal b Z.zero then a else Z.rem a b))
        else if n == N.nat_div then bin (fun a b -> nat (if Z.equal b Z.zero then Z.zero else Z.div a b))
        else if n == N.nat_beq then bin (fun a b -> bool (Z.equal a b))
        else if n == N.nat_ble then bin (fun a b -> bool (Z.leq a b))
        else if n == N.nat_land then bin (fun a b -> nat (Z.logand a b))
        else if n == N.nat_lor then bin (fun a b -> nat (Z.logor a b))
        else if n == N.nat_xor then bin (fun a b -> nat (Z.logxor a b))
        else if n == N.nat_shl then bin (fun a b ->
            if Z.equal a Z.zero then nat Z.zero else begin
              if Z.gt b (Z.of_int 0xFFFFFFFF) then fail "Nat.shiftLeft amount too large";
              let k = Z.to_int b in
              if Z.numbits a / 8 + k / 8 + 1 > Tc.max_nat_bytes then fail "Nat.shiftLeft result too large";
              nat (Z.shift_left a k)
            end)
        else if n == N.nat_shr then bin (fun a b ->
            if Z.gt b (Z.of_int max_int) then nat Z.zero else nat (Z.shift_right a (Z.to_int b)))
        else None
      end else None
    | _ -> None

and whnf st v =
  match v with
  | VNeu n ->
    if n.whnf_f != dummy then n.whnf_f
    else begin
      let rec loop t =
        tick st;
        let t1 = whnf_core st t in
        match reduce_nat st t1 with
        | Some r -> r
        | None ->
          match unfold st t1 with
          | Some t' -> loop t'
          | None -> t1 in
      enter st; cnt st 6;
      let r = loop v in
      leave st;
      n.whnf_f <- r; r
    end
  | _ -> v

(* ------------------------------------------------------------------ types *)
(* The type of a value.  Lambdas and Pi types have no recorded type here
   (callers that need one decline or skip a heuristic). *)
and type_of st v : value =
  match v with
  | VSort l -> VSort (Level.succ l)
  | VNat _ -> nat_type st
  | VStr _ -> string_type st
  | VLam _ -> decline "type of a lambda"
  | VPi _ -> decline "type of a Pi"
  | VNeu n ->
    if n.nty != dummy then n.nty
    else begin
      cnt st 9;
      let h = match n.head with
        | HConst (c, ls) -> const_type st c ls
        | HLocal l -> l.lty
        | HProj (s, i, sv) -> proj_type st s i sv in
      let t = List.fold_right (fun a t ->
          match whnf st t with
          | VPi (_, c) -> inst_thunk st c a
          | _ -> decline "spine of a non-function") n.rargs h in
      n.nty <- t; t
    end

and proj_type st sname idx sv =
  let ty = whnf st (type_of st sv) in
  match ty with
  | VNeu ({ head = HConst (i_name, i_levels); _ } as tn) when Name.equal i_name sname ->
    (match Tc.ind_info st.tc i_name with
     | Some ({ ctors = [ctor]; _ } as iv) when tn.nargs = iv.nparams + iv.nindices ->
       let targs = args_array tn in
       let r = ref (const_type st ctor i_levels) in
       for i = 0 to iv.nparams - 1 do
         match whnf st !r with
         | VPi (_, c) -> r := inst_thunk st c targs.(i)
         | _ -> decline "projection"
       done;
       for j = 0 to idx - 1 do
         match whnf st !r with
         | VPi (_, c) -> r := inst st c (mk_neu st (HProj (i_name, j, sv)) [] 0 (vopen sv))
         | _ -> decline "projection"
       done;
       (match whnf st !r with VPi (d, _) -> force st d | _ -> decline "projection")
     | _ -> decline "projection")
  | _ -> decline "projection"

(* Is [ty] (a type) a proposition? *)
and is_prop st ty =
  match whnf st ty with
  | VPi (d, c) -> is_prop st (inst st c (fresh_local st (force st d)))
  | VSort _ | VNat _ | VStr _ | VLam _ -> false
  | VNeu _ as t ->
    (match whnf st (type_of st t) with
     | VSort l -> Level.normalizes_to_zero l
     | _ -> false)

(* ------------------------------------------------------------ conversion *)
and levels_eq la lb =
  List.compare_lengths la lb = 0 && List.for_all2 Level.is_equiv la lb

(* Bounded syntactic equality of values (Lean's quick check starts with
   structural equality of terms).  [true] means equal; [false] unknown. *)
and same st t s fuel =
  t == s ||
  (!fuel > 0 && begin
      decr fuel;
      match t, s with
      | VSort a, VSort b -> a == b || Level.equal a b
      | VNat a, VNat b -> Z.equal a b
      | VStr a, VStr b -> String.equal a b
      | VPi (d1, c1), VPi (d2, c2) | VLam (d1, c1), VLam (d2, c2) ->
        same_thunk st d1 d2 fuel && same_clo st c1 c2 fuel
      | VNeu a, VNeu b ->
        a.nargs = b.nargs && same_head st a.head b.head fuel &&
        (let rec go l1 l2 = match l1, l2 with
            | x :: r1, y :: r2 -> same_thunk st x y fuel && go r1 r2
            | [], [] -> true
            | _ -> false in
         go a.rargs b.rargs)
      | _ -> false
    end)

and same_head st a b fuel = match a, b with
  | HConst (x, la), HConst (y, lb) ->
    (x == y || Name.equal x y) && List.compare_lengths la lb = 0 && List.for_all2 (fun p q -> p == q || Level.equal p q) la lb
  | HLocal x, HLocal y -> x.lid = y.lid
  | HProj (s1, i1, e1), HProj (s2, i2, e2) -> i1 = i2 && Name.equal s1 s2 && same st e1 e2 fuel
  | _ -> false

and same_thunk st x y fuel =
  x == y ||
  (if x.tv == dummy && y.tv == dummy && x.tterm == y.tterm && x.tsub.sid = y.tsub.sid
      && same_env st x.tenv y.tenv fuel then true
   else same st (force st x) (force st y) fuel)

and same_clo st c1 c2 fuel =
  c1.cbody == c2.cbody && c1.csub.sid = c2.csub.sid && same_env st c1.cenv c2.cenv fuel

and same_env st e1 e2 fuel =
  e1.vals == e2.vals ||
  (let rec go l1 l2 = match l1, l2 with
      | x :: r1, y :: r2 -> (x == y || same_thunk st x y fuel) && go r1 r2
      | [], [] -> true
      | _ -> false in
   go e1.vals e2.vals)

and quick st t s : int =
  if same st t s (ref 256) then (cnt st 5; 1) else
  match t, s with
  | VSort a, VSort b -> if Level.is_equiv a b then 1 else 0
  | VNat a, VNat b -> if Z.equal a b then 1 else 0
  | VStr a, VStr b -> if String.equal a b then 1 else 0
  | VLam (dt, ct), VLam (ds, cs) | VPi (dt, ct), VPi (ds, cs) ->
    let d1 = force st dt and d2 = force st ds in
    if (d1 == d2 || conv st d1 d2) then begin
      let x = fresh_local st d2 in
      if conv st (inst st ct x) (inst st cs x) then 1 else 0
    end else 0
  | VNeu a, VNeu b when PairSet.mem st.success (min a.nid b.nid, max a.nid b.nid) -> 1
  | _ -> -1

and show v = match v with
  | VSort _ -> "Sort" | VPi _ -> "Pi" | VLam _ -> "Lam" | VNat z -> "nat " ^ Z.to_string z | VStr _ -> "str"
  | VNeu { head = HConst (n, _); nargs; _ } -> Printf.sprintf "%s/%d" (Name.to_string n) nargs
  | VNeu { head = HLocal l; nargs; _ } -> Printf.sprintf "x%d/%d" l.lid nargs
  | VNeu { head = HProj (n, i, _); nargs; _ } -> Printf.sprintf "%s.%d/%d" (Name.to_string n) i nargs

and conv st t s =
  t == s ||
  if dbg then begin
    (* O4L_NBE_DBG: print the heads of very deep comparison chains *)
    incr depth;
    if !depth > 3000 then begin
      Printf.eprintf "deep: %s =?= %s\n%!" (show t) (show s);
      if !depth > 3040 then (decr depth; decline "deep")
    end;
    Fun.protect ~finally:(fun () -> decr depth) (fun () -> conv_main st t s)
  end else conv_main st t s

and conv_main st t s =
  begin
    cnt st 4;
    tick st;
    enter st;
    let res = conv_main1 st t s in
    leave st;
    res
  end

and conv_main1 st t s =
  begin
    let r = quick st t s in
    if r >= 0 then r = 1 else begin
      let r = conv_core st t s in
      (match t, s with
       | VNeu a, VNeu b when r -> PairSet.replace st.success (min a.nid b.nid, max a.nid b.nid) ()
       | _ -> ());
      r
    end
  end

and is_bool_true v = match v with
  | VNeu { head = HConst (n, []); nargs = 0; _ } -> Name.equal n Tc.N.bool_true
  | _ -> false

and conv_core st t s =
  if ((not (vopen t)) || st.eager) && is_bool_true s && is_bool_true (whnf st t) then true
  else begin
    let tn = whnf_core ~cheap:true st t and sn = whnf_core ~cheap:true st s in
    let r = if tn != t || sn != s then quick st tn sn else -1 in
    if r >= 0 then r = 1 else begin
      let r = proof_irrel st tn sn in
      if r >= 0 then r = 1 else begin
        match lazy_delta st tn sn with
        | `Eq -> true
        | `Neq -> false
        | `Unknown (tn, sn) ->
          match tn, sn with
          | VNeu { head = HConst (a, la); nargs = 0; _ }, VNeu { head = HConst (b, lb); nargs = 0; _ }
            when Name.equal a b && levels_eq la lb -> true
          | VNeu { head = HLocal x; nargs = 0; _ }, VNeu { head = HLocal y; nargs = 0; _ } when x.lid = y.lid -> true
          | _ ->
            let proj_ok = match tn, sn with
              | VNeu { head = HProj (s1, i1, e1); nargs = 0; _ }, VNeu { head = HProj (s2, i2, e2); nargs = 0; _ }
                when Name.equal s1 s2 && i1 = i2 -> lazy_delta_proj st e1 e2 s1 i1
              | _ -> false in
            proj_ok || begin
              let tnn = whnf_core st tn and snn = whnf_core st sn in
              if tnn != tn || snn != sn then conv st tnn snn
              else conv_app st tn sn || eta st tn sn || eta st sn tn
                   || eta_struct st tn sn || eta_struct st sn tn
                   || (match string_expand st tn sn with -1 -> string_expand st sn tn = 1 | r -> r = 1)
                   || unit_like st tn sn
            end
      end
    end
  end

and proof_irrel st t s =
  match t with
  | VLam _ | VPi _ | VSort _ -> -1
  | _ ->
    match type_of st t with
    | exception Decline _ -> -1
    | tt ->
      if not (is_prop st tt) then -1
      else match type_of st s with
        | exception Decline _ -> -1
        | ts -> if conv st tt ts then 1 else 0

and is_nat_zero st v = match nat_lit_ext st v with Some z -> Z.equal z Z.zero | None -> false

and nat_pred st v = match v with
  | VNat z when not (Z.equal z Z.zero) -> Some (VNat (Z.pred z))
  | VNeu { head = HConst (n, []); nargs = 1; rargs = [a]; _ } when Name.equal n Tc.N.nat_succ -> Some (force st a)
  | _ -> None

and offset st t s =
  if not st.tc.Tc.bi.nat_ok then -1
  else if is_nat_zero st t && is_nat_zero st s then 1
  else match nat_pred st t, nat_pred st s with
    | Some a, Some b -> if conv_core_entry st a b then 1 else 0
    | _ -> -1

and conv_core_entry st a b = a == b || (let r = quick st a b in if r >= 0 then r = 1 else conv_core st a b)

(* one lazy delta step; returns (code, t', s') with code 0 continue,
   1 equal, 2 different, 3 unknown (Tc.lazy_delta_reduction_step) *)
and step st tn sn =
  let unfold_c v = match unfold st v with
    | Some v' -> whnf_core ~cheap:true st v'
    | None -> fail "unfold failed" in
  let proj_app v = match v with
    | VNeu { head = HProj _; _ } -> let v' = whnf_core st v in if v' != v then Some v' else None
    | _ -> None in
  let code, t', s' = match delta_info st tn, delta_info st sn with
    | None, None -> 3, tn, sn
    | Some _, None ->
      (match proj_app sn with Some s' -> 0, tn, s' | None -> 0, unfold_c tn, sn)
    | None, Some _ ->
      (match proj_app tn with Some t' -> 0, t', sn | None -> 0, tn, unfold_c sn)
    | Some d1, Some d2 ->
      let cmp = compare_hints (hints d1) (hints d2) in
      if cmp < 0 then 0, unfold_c tn, sn
      else if cmp > 0 then 0, tn, unfold_c sn
      else begin
        let shortcut = match tn, sn, hints d1 with
          | VNeu a, VNeu b, Regular _ when d1 == d2 && a.nargs > 0 && b.nargs > 0 ->
            let key = (min a.nid b.nid, max a.nid b.nid) in
            if PairSet.mem st.failure key then false
            else begin
              let la = match a.head with HConst (_, l) -> l | _ -> [] in
              let lb = match b.head with HConst (_, l) -> l | _ -> [] in
              if levels_eq la lb && args_eq st a b then true
              else (PairSet.replace st.failure key (); false)
            end
          | _ -> false in
        if shortcut then 1, tn, sn else 0, unfold_c tn, unfold_c sn
      end in
  if code <> 0 then (code, t', s')
  else match quick st t' s' with 1 -> (1, t', s') | 0 -> (2, t', s') | _ -> (0, t', s')

and args_eq st a b =
  a.nargs = b.nargs &&
  (let rec go l1 l2 = match l1, l2 with
      | x :: r1, y :: r2 -> (x == y || conv st (force st x) (force st y)) && go r1 r2
      | [], [] -> true
      | _ -> false in
   go a.rargs b.rargs)

and lazy_delta st tn sn =
  tick st;
  match offset st tn sn with
  | 1 -> `Eq
  | 0 -> `Neq
  | _ ->
    let try_nat =
      if ((not (vopen tn)) && not (vopen sn)) || st.eager then
        match reduce_nat st tn with
        | Some tv -> Some (if conv_core_entry st tv sn then `Eq else `Neq)
        | None -> match reduce_nat st sn with
          | Some sv -> Some (if conv_core_entry st tn sv then `Eq else `Neq)
          | None -> None
      else None in
    match try_nat with
    | Some r -> r
    | None ->
      match step st tn sn with
      | 0, t', s' -> lazy_delta st t' s'
      | 1, _, _ -> `Eq
      | 2, _, _ -> `Neq
      | _, t', s' -> `Unknown (t', s')

and lazy_delta_proj st e1 e2 sname idx =
  tick st;
  match step st e1 e2 with
  | 0, t', s' -> lazy_delta_proj st t' s' sname idx
  | 1, _, _ -> true
  | _, t, s ->
    (match proj_reduce st sname idx t with
     | Some a -> (match proj_reduce st sname idx s with
         | Some b -> conv_core_entry st a b
         | None -> conv_core_entry st t s)
     | None -> conv_core_entry st t s)

and heads_eq st a b = match a, b with
  | HConst (x, la), HConst (y, lb) -> Name.equal x y && levels_eq la lb
  | HLocal x, HLocal y -> x.lid = y.lid
  | HProj (s1, i1, e1), HProj (s2, i2, e2) -> Name.equal s1 s2 && i1 = i2 && conv st e1 e2
  | _ -> false

and conv_app st t s = match t, s with
  | VNeu a, VNeu b when a.nargs > 0 && a.nargs = b.nargs -> heads_eq st a.head b.head && args_eq st a b
  | _ -> false

and eta st t s = match t, s with
  | VLam (d, c), (VNeu _ as s) ->
    (match type_of st s with
     | exception Decline _ -> false
     | ty ->
       match whnf st ty with
       | VPi (sd, _) ->
         let sd = force st sd in
         conv st (force st d) sd &&
         (let x = fresh_local st sd in conv st (inst st c x) (apply st s (of_value x)))
       | _ -> false)
  | _ -> false

and eta_struct st t s =
  match ctor_of st s with
  | Some (_, _, cv, nu) when nu.nargs = cv.cnparams + cv.nfields && Tc.is_non_rec_structure st.tc cv.induct ->
    (match type_of st t, type_of st s with
     | exception Decline _ -> false
     | tt, ts ->
       conv st tt ts &&
       (let args = args_array nu in
        let ok = ref true and i = ref cv.cnparams in
        while !ok && !i < nu.nargs do
          let p = mk_neu st (HProj (cv.induct, !i - cv.cnparams, t)) [] 0 (vopen t) in
          if not (conv st p (force st args.(!i))) then ok := false;
          incr i
        done; !ok))
  | _ -> false

and string_expand st t s =
  match t, s with
  | VStr str, VNeu { head = HConst (n, _); _ } when Name.equal n Tc.N.string_of_list && st.tc.Tc.bi.str_ok ->
    if conv st (whnf st (string_to_ctor st str)) s then 1 else 0
  | _ -> -1

and unit_like st t s =
  match type_of st t with
  | exception Decline _ -> false
  | tt ->
    let tt = whnf st tt in
    match tt with
    | VNeu { head = HConst (n, _); _ } when Tc.is_non_rec_structure st.tc n ->
      (match Tc.ind_info st.tc n with
       | Some { ctors = [ctor]; _ } ->
         (match find st ctor with
          | Some { kind = Ctor { nfields = 0; _ }; _ } ->
            (match type_of st s with exception Decline _ -> false | ts -> conv st tt ts)
          | _ -> false)
       | _ -> false)
    | _ -> false

(* ---------------------------------------------------------------- typing *)
(* A context binds the loose bound variables of the term being checked:
   their values (for evaluation) and their types.  [cid] identifies it for
   the inference memo; closed terms use 0. *)
type cx = { env : env; tys : value list; cid : int }

let empty_cx = { env = empty_env; tys = []; cid = 0 }

let bind st cx (t : thunk) ty = { env = push cx.env t; tys = ty :: cx.tys; cid = fresh_id st }

let eval_cx st cx e = eval st cx.env id_sub e

let check_level st l = Tc.check_level st.tc l

let rec infer st cx e : value =
  match e with
  | BVar { idx; _ } ->
    (try List.nth cx.tys idx with _ -> fail "type checker does not support loose bound variables")
  | FVar _ -> decline "free variable"
  | NatLit { n; _ } ->
    if not st.tc.Tc.bi.nat_ok then fail "Nat literal used, but Nat is not available";
    if Z.numbits n / 8 > Tc.max_nat_bytes then fail "Nat literal too large";
    nat_type st
  | StrLit _ ->
    if not st.tc.Tc.bi.str_ok then fail "String literal used, but String is not available";
    string_type st
  | Sort { l; _ } -> check_level st l; VSort (Level.succ l)
  | Const { n; ls; _ } ->
    let ci = get st n in
    if List.compare_lengths ci.lparams ls <> 0 then
      fail "incorrect number of universe levels for '%s'" (Name.to_string n);
    if ci.unsafe && st.tc.Tc.safety <> Unsafe then
      fail "invalid declaration, it uses unsafe declaration '%s'" (Name.to_string n);
    (match ci.kind with
     | Defn { safety = Partial; _ } when st.tc.Tc.safety = Safe ->
       fail "invalid declaration, safe declaration must not contain partial declaration '%s'" (Name.to_string n)
     | _ -> ());
    List.iter (check_level st) ls;
    const_type st n ls
  | _ when size e < memo_size -> infer_node st cx e
  | _ ->
    let key = (e, if closed e then 0 else cx.cid) in
    match ETbl.find_opt st.infers key with
    | Some t -> t
    | None ->
      let t = infer_node st cx e in
      ETbl.add st.infers key t; t

and infer_node st cx e =
  cnt st 10;
  match e with
  | App _ ->
    let f, args = get_app_args e in
    infer_app st cx f args
  | Lam _ -> decline "infer lambda"
  | Pi { ty; b; _ } ->
    let u = sort_of st cx ty in
    let d = eval_cx st cx ty in
    let x = fresh_local st d in
    let v = sort_of st (bind st cx (of_value x) d) b in
    VSort (Level.mk_imax u v)
  | Let { ty; v; b; _ } ->
    ignore (sort_of st cx ty);
    let tv = eval_cx st cx ty in
    check st cx v tv;
    infer st (bind st cx (mk_thunk st cx.env id_sub v) tv) b
  | Proj { s; idx; e = se; _ } -> infer_proj st cx s idx se
  | _ -> infer st cx e

and infer_app st cx f args =
  let n = Array.length args in
  (* a head lambda is a redex: its arguments are checked against its domains *)
  let rec peel cxb f i =
    match f with
    | Lam { ty; b; _ } when i < n ->
      ignore (sort_of st cxb ty);
      let d = eval_cx st cxb ty in
      check_arg st cx args.(i) d;
      peel (bind st cxb (mk_thunk st cx.env id_sub args.(i)) d) b (i + 1)
    | _ -> (cxb, f, i) in
  let cx', f', i0 = peel cx f 0 in
  let tf = ref (infer st cx' f') in
  for i = i0 to n - 1 do
    match whnf st !tf with
    | VPi (d, c) ->
      check_arg st cx args.(i) (force st d);
      tf := inst_thunk st c (mk_thunk st cx.env id_sub args.(i))
    | _ -> fail "function expected"
  done;
  !tf

and check_arg st cx a d =
  if is_app_of a Tc.N.eager_reduce && get_app_num_args a = 2 then begin
    let saved = st.eager in
    st.eager <- true;
    (match check st cx a d with () -> st.eager <- saved | exception ex -> st.eager <- saved; raise ex)
  end else check st cx a d

and sort_of st cx e =
  match whnf st (infer st cx e) with
  | VSort l -> l
  | _ -> fail "type expected"

and check st cx e (expected : value) =
  match e with
  | Lam { ty; b; _ } ->
    (match whnf st expected with
     | VPi (d', c) ->
       ignore (sort_of st cx ty);
       let d = eval_cx st cx ty in
       if not (conv st d (force st d')) then fail "type mismatch (binder domain)";
       let x = fresh_local st d in
       check st (bind st cx (of_value x) d) b (inst st c x)
     | _ -> decline "lambda against a non-Pi type")
  | Let { ty; v; b; _ } ->
    ignore (sort_of st cx ty);
    let tv = eval_cx st cx ty in
    check st cx v tv;
    check st (bind st cx (mk_thunk st cx.env id_sub v) tv) b expected
  | _ ->
    let t = infer st cx e in
    if not (conv st t expected) then fail "type mismatch"

and infer_proj st cx sname idx se =
  let sty = whnf st (infer st cx se) in
  let bad () = fail "invalid projection" in
  match sty with
  | VNeu ({ head = HConst (i_name, i_levels); _ } as tn) ->
    if not (Name.equal i_name sname) then bad ();
    let iv = match Tc.ind_info st.tc i_name with Some iv -> iv | None -> bad () in
    let ctor = match iv.ctors with [ctor] -> ctor | _ -> bad () in
    if tn.nargs <> iv.nparams + iv.nindices then bad ();
    let ci = get st ctor in
    if List.compare_lengths ci.lparams i_levels <> 0 then bad ();
    let sv = eval_cx st cx se in
    let targs = args_array tn in
    let r = ref (const_type st ctor i_levels) in
    for i = 0 to iv.nparams - 1 do
      match whnf st !r with
      | VPi (_, c) -> r := inst_thunk st c targs.(i)
      | _ -> bad ()
    done;
    let is_prop_type = is_prop st sty in
    for j = 0 to idx - 1 do
      match whnf st !r with
      | VPi (d, c) ->
        if is_prop_type && not (is_prop st (force st d)) then begin
          (* Tc only requires this when the codomain depends on the field;
             this prototype does not track dependency, so it leaves the
             case to Tc *)
          decline "projection past a non-propositional field"
        end;
        r := inst st c (mk_neu st (HProj (i_name, j, sv)) [] 0 (vopen sv))
      | _ -> bad ()
    done;
    (match whnf st !r with
     | VPi (d, _) ->
       let d = force st d in
       if is_prop_type && not (is_prop st d) then bad ();
       d
     | _ -> bad ())
  | _ -> bad ()

(* ------------------------------------------------------------------ entry *)
let fuel = match Sys.getenv_opt "O4L_NBE_FUEL" with Some v -> int_of_string v | None -> 20_000_000

let create tc = {
  tc; next = 0; fuel; eager = false; rdepth = 0; counts = Array.make 12 0;
  delta = KTbl.create 64; ctype = KTbl.create 64; subs = KTbl.create 16;
  evals = ETbl.create 256; infers = ETbl.create 256;
  success = PairSet.create 64; failure = PairSet.create 16;
}

(* Check that [v] has type [ci.ty] (whose well-formedness the caller has
   checked).  [tc] carries the environment view, universe parameters and
   safety of the declaration. *)
let check_decl (tc : Tc.ctx) (ci : cinfo) v =
  let st = create tc in
  let fin () = if stats_on then Array.iteri (fun i c -> ignore (Atomic.fetch_and_add totals.(i) c)) st.counts in
  match
    let ty = eval st empty_env id_sub ci.ty in
    check st empty_cx v ty
  with
  | () -> fin ()
  | exception e -> fin (); raise e

let print_stats () =
  if stats_on then
    Array.iteri (fun i n -> Printf.eprintf "nbe-count %-10s %d\n" n (Atomic.get totals.(i))) counter_names

(* counters, for --stats *)
let accepted = Atomic.make 0
let fallbacks = Atomic.make 0
let declines = Atomic.make 0
