(* The type checker: type inference, weak head normalisation and definitional
   equality.  This follows the structure (and, where it matters for
   completeness, the heuristics) of Lean 4's kernel/type_checker.cpp. *)
open Expr
open Env

exception Kernel_error of string
let fail fmt = Printf.ksprintf (fun s -> raise (Kernel_error s)) fmt

module Tbl = Expr.Tbl
module PTbl = Hashtbl.Make (struct
    type nonrec t = Expr.t * Expr.t
    let equal (a, b) (c, d) = Expr.equal a c && Expr.equal b d
    let hash (a, b) = Hc.mix (Expr.hash a) (Expr.hash b)
  end)

(* ---- well-known names ---- *)
module N = struct
  let n = Name.of_string
  let nat = n "Nat" let nat_zero = n "Nat.zero" let nat_succ = n "Nat.succ"
  let nat_add = n "Nat.add" let nat_sub = n "Nat.sub" let nat_mul = n "Nat.mul"
  let nat_pow = n "Nat.pow" let nat_gcd = n "Nat.gcd" let nat_mod = n "Nat.mod"
  let nat_div = n "Nat.div" let nat_beq = n "Nat.beq" let nat_ble = n "Nat.ble"
  let nat_land = n "Nat.land" let nat_lor = n "Nat.lor" let nat_xor = n "Nat.xor"
  let nat_shl = n "Nat.shiftLeft" let nat_shr = n "Nat.shiftRight"
  let bool = n "Bool" let bool_true = n "Bool.true" let bool_false = n "Bool.false"
  let string = n "String" let string_of_list = n "String.ofList"
  let char = n "Char" let char_of_nat = n "Char.ofNat"
  let list = n "List" let list_nil = n "List.nil" let list_cons = n "List.cons"
  let quot = n "Quot" let quot_mk = n "Quot.mk" let quot_lift = n "Quot.lift" let quot_ind = n "Quot.ind"
  let eq = n "Eq" let eq_refl = n "Eq.refl"
  let eager_reduce = n "eagerReduce"
  let dontcare = n "dontcare"
end

(* Which literal / builtin extensions are sound to use in this environment
   (decided once, see [Builtins]). *)
type builtins = { nat_ok : bool; str_ok : bool; quot_ok : bool }

type ctx = {
  env : Env.t;
  bi : builtins;
  pos : int;                                   (* constants with pos < this are visible *)
  local : cinfo Name.Tbl.t;           (* constants of the block being checked *)
  mutable lparams : Name.t list option;        (* universe parameters in scope *)
  safety : safety;
  infer_tbl : Expr.t Emap.t;
  infer_only_tbl : Expr.t Emap.t;
  whnf_core_tbl : Expr.t Emap.t;
  whnf_tbl : Expr.t Emap.t;
  unfold_tbl : Expr.t Emap.t;
  success : Pset.t;
  failure : Pset.t;
  mutable eager : bool;
}

let max_nat_bytes = 128 * 1024 * 1024

let create ?(local = Name.Tbl.create 8) ?(safety = Safe) env bi pos = {
  env; bi; pos; local; lparams = None; safety;
  infer_tbl = Emap.create Emap.dummy_key 64; infer_only_tbl = Emap.create Emap.dummy_key 64;
  whnf_core_tbl = Emap.create Emap.dummy_key 64; whnf_tbl = Emap.create Emap.dummy_key 64;
  unfold_tbl = Emap.create Emap.dummy_key 16;
  success = Pset.create 16; failure = Pset.create 16; eager = false;
}

let find_global c n =
  match Name.Tbl.find c.env.consts n with
  | ci when ci.pos >= 0 && ci.pos < c.pos -> Some ci
  | _ -> None
  | exception Not_found -> None

let find c n =
  if Name.Tbl.length c.local = 0 then find_global c n else
  match Name.Tbl.find_opt c.local n with
  | Some _ as r -> r
  | None ->
    find_global c n

let get c n = match find c n with
  | Some ci -> ci
  | None -> fail "unknown constant '%s'" (Name.to_string n)

let mk_const n = Expr.const n []
(* Built eagerly at startup (before the environment is frozen, so they are
   shared global nodes).  These must not be [lazy]: forcing one lazy value
   from two domains at once raises CamlinternalLazy.Undefined in OCaml 5. *)
let c_nat = mk_const N.nat
let c_nat_zero = mk_const N.nat_zero
let c_nat_succ = mk_const N.nat_succ
let c_bool_true = mk_const N.bool_true
let c_bool_false = mk_const N.bool_false
let c_string = mk_const N.string
let dontcare = mk_const N.dontcare

let is_sort = function Sort _ -> true | _ -> false
let is_pi = function Pi _ -> true | _ -> false
let is_lambda = function Lam _ -> true | _ -> false
let sort_level = function Sort { l; _ } -> l | _ -> assert false

let check_level c l =
  match c.lparams with
  | None -> ()
  | Some ps ->
    match Level.undef_param ps l with
    | Some n -> fail "invalid reference to undefined universe level parameter '%s'" (Name.to_string n)
    | None -> ()

(* ---------- literals ---------- *)
let is_nat_lit_ext e = match e with
  | NatLit _ -> true
  | Const { n; ls = []; _ } -> n == N.nat_zero || Name.equal n N.nat_zero
  | _ -> false
let nat_val = function NatLit { n; _ } -> n | _ -> Z.zero

let nat_lit_to_constructor = function
  | NatLit { n; _ } ->
    if Z.equal n Z.zero then c_nat_zero
    else app (c_nat_succ) (natlit (Z.pred n))
  | e -> e

(* decode UTF-8 into code points (invalid bytes are taken as is) *)
let utf8_decode s =
  let n = String.length s in
  let res = ref [] in
  let i = ref 0 in
  while !i < n do
    let c = Char.code s.[!i] in
    let len, init =
      if c < 0x80 then 1, c else if c < 0xE0 then 2, c land 0x1F
      else if c < 0xF0 then 3, c land 0x0F else 4, c land 0x07 in
    let v = ref init in
    for k = 1 to len - 1 do
      if !i + k < n then v := (!v lsl 6) lor (Char.code s.[!i + k] land 0x3F)
    done;
    res := !v :: !res;
    i := !i + len
  done;
  List.rev !res

let string_lit_to_constructor s =
  let char_ty = mk_const N.char in
  let cons = app (Expr.const N.list_cons [Level.zero]) char_ty in
  let nil = app (Expr.const N.list_nil [Level.zero]) char_ty in
  let ofnat = mk_const N.char_of_nat in
  let cps = utf8_decode s in
  let l = List.fold_right (fun cp acc -> app (app cons (app ofnat (natlit (Z.of_int cp)))) acc) cps nil in
  app (mk_const N.string_of_list) l

(* ---------- inductive helpers ---------- *)
let ind_info c n = match find c n with
  | Some ({ kind = Induct i; _ }) -> Some i | _ -> None
[@@inline]

let is_non_rec_structure c n = match find c n with
  | Some { kind = Induct { ctors = [_]; nindices = 0; is_rec = false; _ }; _ } -> true
  | _ -> false

let is_ctor_app c e = match get_app_fn e with
  | Const { n; _ } -> (match find c n with Some { kind = Ctor _; _ } -> Some n | _ -> None)
  | _ -> None

let instantiate_type_lparams ci ls = instantiate_lparams ci.ty ci.lparams ls

(* ---------- inference ---------- *)
let rec infer_core c e infer_only : Expr.t =
  if not (closed e) then fail "type checker does not support loose bound variables";
  let tbl = if infer_only then c.infer_only_tbl else c.infer_tbl in
  match Emap.find tbl e with
  | r -> r
  | exception Not_found ->
    let r = match e with
      | NatLit { n; _ } ->
        if not c.bi.nat_ok then fail "Nat literal used, but Nat is not available";
        if Z.numbits n / 8 > max_nat_bytes then fail "Nat literal too large";
        c_nat
      | StrLit _ ->
        if not c.bi.str_ok then fail "String literal used, but String is not available";
        c_string
      | Proj { s; idx; e = st; _ } -> infer_proj c s idx st e infer_only
      | FVar { ty; _ } -> ty
      | BVar _ -> assert false
      | Sort { l; _ } -> if not infer_only then check_level c l; sort (Level.succ l)
      | Const { n; ls; _ } -> infer_const c n ls infer_only
      | Lam _ -> infer_lambda c e infer_only
      | Pi _ -> infer_pi c e infer_only
      | App _ -> infer_app c e infer_only
      | Let _ -> infer_let c e infer_only in
    Emap.add tbl e r; r

and infer_const c n ls infer_only =
  let ci = get c n in
  if List.compare_lengths ci.lparams ls <> 0 then
    fail "incorrect number of universe levels for '%s'" (Name.to_string n);
  if not infer_only then begin
    if ci.unsafe && c.safety <> Unsafe then
      fail "invalid declaration, it uses unsafe declaration '%s'" (Name.to_string n);
    (match ci.kind with
     | Defn { safety = Partial; _ } when c.safety = Safe ->
       fail "invalid declaration, safe declaration must not contain partial declaration '%s'" (Name.to_string n)
     | _ -> ());
    List.iter (check_level c) ls
  end;
  instantiate_type_lparams ci ls

and infer_lambda c e infer_only =
  let fvars = Vec.create () in
  let rec go e = match e with
    | Lam { ty; b; _ } ->
      let d = instantiate_rev_sub ty (Vec.data fvars) (Vec.length fvars) in
      if not infer_only then ignore (ensure_sort c (infer_core c d infer_only));
      Vec.push fvars (mk_fvar d);
      go b
    | _ -> e in
  let body = go e in
  let xs = Vec.to_array fvars in
  let r = infer_core c (instantiate_rev body xs) infer_only in
  let r = cheap_beta_reduce r in
  mk_pi xs r

and infer_pi c e infer_only =
  let fvars = Vec.create () in
  let us = ref [] in
  let rec go e = match e with
    | Pi { ty; b; _ } ->
      let d = instantiate_rev_sub ty (Vec.data fvars) (Vec.length fvars) in
      let s = ensure_sort c (infer_core c d infer_only) in
      us := sort_level s :: !us;
      Vec.push fvars (mk_fvar d);
      go b
    | _ -> e in
  let body = go e in
  let xs = Vec.to_array fvars in
  let s = ensure_sort c (infer_core c (instantiate_rev body xs) infer_only) in
  let r = List.fold_left (fun r u -> Level.mk_imax u r) (sort_level s) !us in
  sort r

and infer_app c e infer_only =
  if not infer_only then begin
    match e with
    | App { f; a; _ } ->
      let f_type = ensure_pi c (infer_core c f false) in
      let a_type = infer_core c a false in
      (match f_type with
       | Pi { ty = d_type; b; _ } ->
         let ok =
           if is_app_of a N.eager_reduce && get_app_num_args a = 2 then begin
             let saved = c.eager in
             c.eager <- true;
             let r = (try is_def_eq c a_type d_type with ex -> c.eager <- saved; raise ex) in
             c.eager <- saved; r
           end else is_def_eq c a_type d_type in
         if not ok then
           fail "application type mismatch: argument %s has type %s but is expected to have type %s"
             (to_string ~max:300 a) (to_string ~max:300 a_type) (to_string ~max:300 d_type);
         instantiate1 b a
       | _ -> assert false)
    | _ -> assert false
  end else begin
    let f, args = get_app_args e in
    let f_type = ref (infer_core c f true) in
    let j = ref 0 in
    let nargs = Array.length args in
    for i = 0 to nargs - 1 do
      match !f_type with
      | Pi { b; _ } -> f_type := b
      | _ ->
        let t = instantiate_args !f_type args !j i in
        (match ensure_pi c t with
         | Pi { b; _ } -> f_type := b
         | _ -> assert false);
        j := i
    done;
    instantiate_args !f_type args !j nargs
  end

and infer_let c e infer_only =
  let fvars = Vec.create () in
  let rec go e = match e with
    | Let { ty; v; b; _ } ->
      let n = Vec.length fvars in
      let ty = instantiate_rev_sub ty (Vec.data fvars) n in
      let v = instantiate_rev_sub v (Vec.data fvars) n in
      if not infer_only then begin
        ignore (ensure_sort c (infer_core c ty infer_only));
        let vt = infer_core c v infer_only in
        if not (is_def_eq c vt ty) then fail "let value type mismatch"
      end;
      Vec.push fvars (mk_fvar ~v ty);
      go b
    | _ -> e in
  let body = go e in
  let xs = Vec.to_array fvars in
  let r = infer_core c (instantiate_rev body xs) infer_only in
  let r = cheap_beta_reduce r in
  mk_binding false xs (Array.length xs) r true

and infer_proj c sname idx st e infer_only =
  let ty = whnf c (infer_core c st infer_only) in
  let bad () = fail "invalid projection %s" (to_string ~max:300 e) in
  let i_head, args = get_app_args ty in
  let i_name, i_levels = match i_head with Const { n; ls; _ } -> n, ls | _ -> bad () in
  if not (Name.equal i_name sname) then bad ();
  let iv = match ind_info c i_name with Some iv -> iv | None -> bad () in
  let ctor = match iv.ctors with [ctor] -> ctor | _ -> bad () in
  if Array.length args <> iv.nparams + iv.nindices then bad ();
  let ci = get c ctor in
  if List.compare_lengths ci.lparams i_levels <> 0 then bad ();
  let r = ref (instantiate_type_lparams ci i_levels) in
  for i = 0 to iv.nparams - 1 do
    match whnf c !r with
    | Pi { b; _ } -> r := instantiate1 b args.(i)
    | _ -> bad ()
  done;
  let is_prop_type = is_prop c ty in
  for i = 0 to idx - 1 do
    match whnf c !r with
    | Pi { ty = d; b; _ } ->
      if not (closed b) then begin
        if is_prop_type && not (is_prop c d) then bad ();
        r := instantiate1 b (proj i_name i st)
      end else r := b
    | _ -> bad ()
  done;
  match whnf c !r with
  | Pi { ty = d; _ } ->
    if is_prop_type && not (is_prop c d) then bad ();
    d
  | _ -> bad ()

and cheap_beta_reduce e =
  match e with
  | App _ ->
    let fn, args = get_app_args e in
    if not (is_lambda fn) then e else begin
      let n = Array.length args in
      let rec strip fn i = match fn with
        | Lam { b; _ } when i < n -> strip b (i + 1)
        | _ -> (fn, i) in
      let fn, i = strip fn 0 in
      if closed fn then mk_app_sub fn args i n
      else match fn with
        | BVar { idx; _ } -> mk_app_sub args.(i - idx - 1) args i n
        | _ -> e
    end
  | _ -> e

and ensure_sort c e =
  if is_sort e then e else
    let e' = whnf c e in
    if is_sort e' then e' else fail "type expected: %s" (to_string ~max:300 e)

and ensure_pi c e =
  if is_pi e then e else
    let e' = whnf c e in
    if is_pi e' then e' else fail "function expected: %s" (to_string ~max:300 e)

and infer c e = infer_core c e true
and check c e = infer_core c e false

and is_prop c e =
  let s = ensure_sort c (infer c e) in
  Level.normalizes_to_zero (sort_level s)

(* ---------- reduction ---------- *)
and whnf_core ?(cheap_rec = false) ?(cheap_proj = false) c e =
  match e with
  | BVar _ | Sort _ | Pi _ | Const _ | Lam _ | NatLit _ | StrLit _ -> e
  | FVar { v = None; _ } -> e
  | FVar { v = Some v; _ } -> whnf_core ~cheap_rec ~cheap_proj c v
  | App _ | Let _ | Proj _ ->
    match Emap.find c.whnf_core_tbl e with
    | r -> r
    | exception Not_found ->
      let cache = not cheap_rec && not cheap_proj in
      let r = match e with
        | Proj { s; idx; e = st; _ } ->
          (match reduce_proj c s idx st cheap_rec cheap_proj with
           | Some m -> whnf_core ~cheap_rec ~cheap_proj c m
           | None -> e)
        | Let { v; b; _ } -> whnf_core ~cheap_rec ~cheap_proj c (instantiate1 b v)
        | App _ ->
          let f0, args = get_app_args e in
          let f = whnf_core ~cheap_rec ~cheap_proj c f0 in
          (match f with
           | Lam _ ->
             let n = Array.length args in
             let rec strip f m = match f with
               | Lam { b; _ } when m < n -> strip b (m + 1)
               | _ -> (f, m) in
             let body, m = strip f 0 in
             (* bvar k := args.(m - 1 - k) *)
             let r = instantiate_args body args 0 m in
             whnf_core ~cheap_rec ~cheap_proj c (mk_app_sub r args m n)
           | _ when f == f0 || Expr.equal f f0 ->
             (match reduce_recursor c e cheap_rec cheap_proj with
              | Some r -> whnf_core ~cheap_rec ~cheap_proj c r
              | None -> e)
           | _ -> whnf_core ~cheap_rec ~cheap_proj c (mk_app_arr f args))
        | _ -> assert false in
      if cache then Emap.add c.whnf_core_tbl e r;
      r

and reduce_proj_core c st sname idx =
  let st = match st with StrLit { s; _ } -> whnf c (string_lit_to_constructor s) | _ -> st in
  let mk, args = get_app_args st in
  match mk with
  | Const { n; _ } ->
    (match find c n with
     | Some { kind = Ctor { induct; cnparams = nparams; _ }; _ } when Name.equal induct sname ->
       if nparams + idx < Array.length args then Some args.(nparams + idx) else None
     | _ -> None)
  | _ -> None

and reduce_proj c sname idx st cheap_rec cheap_proj =
  let st = if cheap_proj then whnf_core ~cheap_rec ~cheap_proj c st else whnf c st in
  reduce_proj_core c st sname idx

and reduce_recursor c e cheap_rec cheap_proj =
  match get_app_fn e with
  | Const { n; ls; _ } ->
    (match find c n with
     | Some ({ kind = Quot (QLift | QInd); _ } as ci) when c.bi.quot_ok -> quot_reduce c ci e
     | Some ({ kind = Recursor r; _ } as ci) -> inductive_reduce_rec c ci r ls e cheap_rec cheap_proj
     | _ -> None)
  | _ -> None

and quot_reduce c ci e =
  let mk_pos, arg_pos = match ci.kind with Quot QLift -> 5, 3 | _ -> 4, 3 in
  let _, args = get_app_args e in
  let nargs = Array.length args in
  if nargs <= mk_pos then None else begin
    let mk = whnf c args.(mk_pos) in
    match get_app_fn mk with
    | Const { n; _ } when (match find c n with Some { kind = Quot QCtor; _ } -> true | _ -> false)
                          && get_app_num_args mk = 3 ->
      let a = match mk with App { a; _ } -> a | _ -> assert false in
      let r = app args.(arg_pos) a in
      Some (mk_app_sub r args (mk_pos + 1) nargs)
    | _ -> None
  end

and to_ctor_when_k c ci (r : _) major nparams =
  (* r : recursor data, ci : recursor constant *)
  let app_type = whnf c (infer c major) in
  let induct = match r with `Induct n -> n in
  match get_app_fn app_type with
  | Const { n; ls; _ } when Name.equal n induct ->
    (match ind_info c n with
     | Some { ctors = ctor :: _; _ } ->
       let _, args = get_app_args app_type in
       if Array.length args < nparams then major else begin
         let new_ctor_app = mk_app_sub (Expr.const ctor ls) args 0 nparams in
         let new_type = infer c new_ctor_app in
         if is_def_eq c app_type new_type then new_ctor_app else major
       end
     | _ -> major)
  | _ -> major

and major_induct c ci (nparams, nmotives, nminors, nindices) =
  (* The inductive type of the major premise, read off the recursor type. *)
  let rec skip t k = match t with
    | Pi { b; _ } when k > 0 -> skip b (k - 1)
    | Pi { ty; _ } -> (match get_app_fn ty with Const { n; _ } -> Some n | _ -> None)
    | _ -> None in
  skip ci.ty (nparams + nmotives + nminors + nindices)

and inductive_reduce_rec c ci r ls e cheap_rec cheap_proj =
  match r with
  | { rnparams = nparams; nmotives; nminors; rnindices = nindices; rules; k; _ } ->
    let _, rec_args = get_app_args e in
    let major_idx = nparams + nmotives + nminors + nindices in
    let nargs = Array.length rec_args in
    if major_idx >= nargs then None else begin
      let induct = major_induct c ci (nparams, nmotives, nminors, nindices) in
      let major = rec_args.(major_idx) in
      let major = match k, induct with
        | true, Some ind -> to_ctor_when_k c ci (`Induct ind) major nparams
        | _ -> major in
      let w x = if cheap_rec then whnf_core ~cheap_rec ~cheap_proj c x else whnf c x in
      let major = w major in
      let major = match major with
        | NatLit _ -> nat_lit_to_constructor major
        | StrLit { s; _ } -> w (string_lit_to_constructor s)
        | _ -> (match induct with
            | Some ind -> to_ctor_when_structure c ind major
            | None -> major) in
      match get_app_fn major with
      | Const { n = cn; _ } ->
        (match List.find_opt (fun rl -> Name.equal rl.r_ctor cn) rules with
         | None -> None
         | Some rule ->
           let _, major_args = get_app_args major in
           let nma = Array.length major_args in
           if rule.r_nfields > nma then None
           else if List.compare_lengths ls ci.lparams <> 0 then None
           else begin
             let rhs = instantiate_lparams rule.r_rhs ci.lparams ls in
             let rhs = mk_app_sub rhs rec_args 0 (nparams + nmotives + nminors) in
             let np = nma - rule.r_nfields in
             let rhs = mk_app_sub rhs major_args np nma in
             Some (mk_app_sub rhs rec_args (major_idx + 1) nargs)
           end)
      | _ -> None
    end

and to_ctor_when_structure c induct e =
  if not (is_non_rec_structure c induct) || is_ctor_app c e <> None then e
  else begin
    let e_type = whnf c (infer c e) in
    match get_app_fn e_type with
    | Const { n; ls; _ } when Name.equal n induct ->
      if is_prop c e_type then e else expand_eta_struct c e_type e
    | _ -> e
  end

and expand_eta_struct c e_type e =
  let i_head, args = get_app_args e_type in
  match i_head with
  | Const { n; ls; _ } ->
    (match ind_info c n with
     | Some { ctors = ctor :: _; _ } ->
       (match find c ctor with
        | Some { kind = Ctor { cnparams = nparams; nfields; _ }; _ } ->
          let r = ref (mk_app_sub (Expr.const ctor ls) args 0 (min nparams (Array.length args))) in
          for i = 0 to nfields - 1 do r := app !r (proj n i e) done;
          !r
        | _ -> e)
     | _ -> e)
  | _ -> e

and is_delta c e =
  match get_app_fn e with
  | Const { n; ls; _ } ->
    (match find c n with
     | Some ci when has_value ci && List.compare_lengths ls ci.lparams = 0 -> Some ci
     | _ -> None)
  | _ -> None

and unfold_definition_core c e =
  match e with
  | Const { ls; _ } ->
    (match is_delta c e with
     | Some ci ->
       let v = match value ci with Some v -> v | None -> assert false in
       if (match ls with [] -> true | _ -> false) then Some v
       else (match Emap.find c.unfold_tbl e with
           | r -> Some r
           | exception Not_found ->
             let r = instantiate_lparams v ci.lparams ls in
             Emap.add c.unfold_tbl e r; Some r)
     | None -> None)
  | _ -> None

and unfold_definition c e =
  match e with
  | App _ ->
    let f0, args = get_app_args e in
    (match unfold_definition_core c f0 with
     | Some f -> Some (mk_app_arr f args)
     | None -> None)
  | _ -> unfold_definition_core c e

and nat_bin c e (f : Z.t -> Z.t -> Z.t option) =
  match e with
  | App { f = App { a = a1; _ }; a = a2; _ } ->
    let a1 = whnf c a1 in
    if not (is_nat_lit_ext a1) then None else
      let a2 = whnf c a2 in
      if not (is_nat_lit_ext a2) then None else
        (match f (nat_val a1) (nat_val a2) with
         | Some r -> Some (natlit r)
         | None -> None)
  | _ -> None

and nat_pred c e (f : Z.t -> Z.t -> bool) =
  match e with
  | App { f = App { a = a1; _ }; a = a2; _ } ->
    let a1 = whnf c a1 in
    if not (is_nat_lit_ext a1) then None else
      let a2 = whnf c a2 in
      if not (is_nat_lit_ext a2) then None else
        Some (if f (nat_val a1) (nat_val a2) then c_bool_true else c_bool_false)
  | _ -> None

and reduce_nat c e =
  if not c.bi.nat_ok then None else
    match e with
    | App { f = Const { n; ls = []; _ }; a; _ } when n == N.nat_succ ->
      let a = whnf c a in
      if is_nat_lit_ext a then Some (natlit (Z.succ (nat_val a))) else None
    | App { f = App { f = Const { n; ls = []; _ }; _ }; _ } ->
      let size_ok r = if Z.numbits r / 8 > max_nat_bytes then fail "Nat numeral too large" else Some r in
      if n == N.nat_add then nat_bin c e (fun a b -> size_ok (Z.add a b))
      else if n == N.nat_sub then nat_bin c e (fun a b -> Some (if Z.leq a b then Z.zero else Z.sub a b))
      else if n == N.nat_mul then nat_bin c e (fun a b -> size_ok (Z.mul a b))
      else if n == N.nat_pow then nat_bin c e (fun a b ->
          if Z.gt b (Z.of_int 0xFFFFFFFF) then fail "Nat.pow exponent too large";
          let k = Z.to_int b in
          if Z.gt a Z.one && k <> 0 && (Z.numbits a / 8 + 1) > max_nat_bytes / k then fail "Nat.pow result too large";
          Some (Z.pow a k))
      else if n == N.nat_gcd then nat_bin c e (fun a b -> Some (Z.gcd a b))
      else if n == N.nat_mod then nat_bin c e (fun a b -> Some (if Z.equal b Z.zero then a else Z.rem a b))
      else if n == N.nat_div then nat_bin c e (fun a b -> Some (if Z.equal b Z.zero then Z.zero else Z.div a b))
      else if n == N.nat_beq then nat_pred c e Z.equal
      else if n == N.nat_ble then nat_pred c e Z.leq
      else if n == N.nat_land then nat_bin c e (fun a b -> Some (Z.logand a b))
      else if n == N.nat_lor then nat_bin c e (fun a b -> Some (Z.logor a b))
      else if n == N.nat_xor then nat_bin c e (fun a b -> Some (Z.logxor a b))
      else if n == N.nat_shl then nat_bin c e (fun a b ->
          if Z.equal a Z.zero then Some Z.zero else begin
            if Z.gt b (Z.of_int 0xFFFFFFFF) then fail "Nat.shiftLeft amount too large";
            let k = Z.to_int b in
            if Z.numbits a / 8 + k / 8 + 1 > max_nat_bytes then fail "Nat.shiftLeft result too large";
            Some (Z.shift_left a k)
          end)
      else if n == N.nat_shr then nat_bin c e (fun a b ->
          if Z.gt b (Z.of_int max_int) then Some Z.zero else Some (Z.shift_right a (Z.to_int b)))
      else None
    | _ -> None

and whnf c e =
  match e with
  | BVar _ | Sort _ | Pi _ | NatLit _ | StrLit _ -> e
  | FVar { v = None; _ } -> e
  | _ ->
    match Emap.find c.whnf_tbl e with
    | r -> r
    | exception Not_found ->
      let rec loop t =
        let t1 = whnf_core c t in
        match reduce_nat c t1 with
        | Some v -> v
        | None ->
          match unfold_definition c t1 with
          | Some t' -> loop t'
          | None -> t1 in
      let r = loop e in
      Emap.add c.whnf_tbl e r; r

(* ---------- definitional equality ---------- *)
and is_def_eq_levels ls1 ls2 = match ls1, ls2 with
  | [], [] -> true
  | a :: r1, b :: r2 -> Level.is_equiv a b && is_def_eq_levels r1 r2
  | _ -> false

and is_def_eq_binding c t s =
  let subst = Vec.create () in
  (* only continue while both have the same binder kind *)
  let rec go' t s = match t, s with
    | Lam _, Lam _ | Pi _, Pi _ -> go_one t s
    | _ -> let xs = Vec.to_array subst in is_def_eq c (instantiate_rev t xs) (instantiate_rev s xs)
  and go_one t s =
    let tt, tb, st, sb = match t, s with
      | Lam { ty = tt; b = tb; _ }, Lam { ty = st; b = sb; _ } -> tt, tb, st, sb
      | Pi { ty = tt; b = tb; _ }, Pi { ty = st; b = sb; _ } -> tt, tb, st, sb
      | _ -> assert false in
    let n = Vec.length subst in
    let var_s_type = ref None in
    let ok =
      if tt != st then begin
        let vs = instantiate_rev_sub st (Vec.data subst) n in
        var_s_type := Some vs;
        let vt = instantiate_rev_sub tt (Vec.data subst) n in
        is_def_eq c vt vs
      end else true in
    if not ok then false else begin
      if not (closed tb) || not (closed sb) then begin
        let vs = match !var_s_type with Some v -> v | None -> instantiate_rev_sub st (Vec.data subst) n in
        Vec.push subst (mk_fvar vs)
      end else Vec.push subst (dontcare);
      match t, tb, sb with
      | Lam _, Lam _, Lam _ | Pi _, Pi _, Pi _ -> go_one tb sb
      | _ -> let xs = Vec.to_array subst in is_def_eq c (instantiate_rev tb xs) (instantiate_rev sb xs)
    end in
  go' t s

and quick_is_def_eq c t s : int (* 1 true, 0 false, -1 unknown *) =
  if Expr.equal t s || succeeded_before c t s then 1
  else match t, s with
    | Lam _, Lam _ | Pi _, Pi _ -> if is_def_eq_binding c t s then 1 else 0
    | Sort { l = l1; _ }, Sort { l = l2; _ } -> if Level.is_equiv l1 l2 then 1 else 0
    | NatLit { n = a; _ }, NatLit { n = b; _ } -> if Z.equal a b then 1 else 0
    | StrLit { s = a; _ }, StrLit { s = b; _ } -> if String.equal a b then 1 else 0
    | _ -> -1

and is_def_eq_args c t s =
  match t, s with
  | App { f = tf; a = ta; _ }, App { f = sf; a = sa; _ } ->
    is_def_eq c ta sa && is_def_eq_args c tf sf
  | App _, _ | _, App _ -> false
  | _ -> true

and try_eta_expansion_core c t s =
  match t, s with
  | Lam _, _ when not (is_lambda s) ->
    (match whnf c (infer c s) with
     | Pi { ty; _ } -> is_def_eq c t (lam ty (app s (bvar 0)))
     | _ -> false)
  | _ -> false

and try_eta_expansion c t s = try_eta_expansion_core c t s || try_eta_expansion_core c s t

and try_eta_struct_core c t s =
  match get_app_fn s with
  | Const { n; _ } ->
    (match find c n with
     | Some { kind = Ctor { induct; cnparams = nparams; nfields; _ }; _ } ->
       if get_app_num_args s <> nparams + nfields then false
       else if not (is_non_rec_structure c induct) then false
       else if not (is_def_eq c (infer c t) (infer c s)) then false
       else begin
         let _, args = get_app_args s in
         let ok = ref true in
         let i = ref nparams in
         while !ok && !i < Array.length args do
           if not (is_def_eq c (proj induct (!i - nparams) t) args.(!i)) then ok := false;
           incr i
         done;
         !ok
       end
     | _ -> false)
  | _ -> false

and try_eta_struct c t s = try_eta_struct_core c t s || try_eta_struct_core c s t

and is_def_eq_app c t s =
  match t, s with
  | App _, App _ ->
    let tf, targs = get_app_args t and sf, sargs = get_app_args s in
    Array.length targs = Array.length sargs && is_def_eq c tf sf &&
    (let ok = ref true and i = ref 0 in
     while !ok && !i < Array.length targs do
       if not (is_def_eq c targs.(!i) sargs.(!i)) then ok := false; incr i
     done; !ok)
  | _ -> false

and is_def_eq_proof_irrel c t s =
  let t_type = infer c t in
  if not (is_prop c t_type) then -1
  else if is_def_eq c t_type (infer c s) then 1 else 0

and failed_before c t s = Pset.mem c.failure t s
and cache_failure c t s = Pset.add c.failure t s
and succeeded_before c t s = Pset.mem c.success t s
and cache_success c t s = Pset.add c.success t s

and try_unfold_proj_app c e =
  match get_app_fn e with
  | Proj _ -> let e' = whnf_core c e in if not (Expr.equal e' e) then Some e' else None
  | _ -> None

(* returns: 0 continue, 1 equal, 2 different, 3 unknown *)
and lazy_delta_reduction_step c (tn : Expr.t ref) (sn : Expr.t ref) =
  let unfold e = match unfold_definition c e with
    | Some e' -> whnf_core ~cheap_proj:true c e'
    | None -> fail "unfold failed" in
  let dt = is_delta c !tn and ds = is_delta c !sn in
  let res = match dt, ds with
    | None, None -> 3
    | Some _, None ->
      (match try_unfold_proj_app c !sn with
       | Some s' -> sn := s'
       | None -> tn := unfold !tn); 0
    | None, Some _ ->
      (match try_unfold_proj_app c !tn with
       | Some t' -> tn := t'
       | None -> sn := unfold !sn); 0
    | Some d1, Some d2 ->
      let cmp = compare_hints (hints d1) (hints d2) in
      if cmp < 0 then (tn := unfold !tn; 0)
      else if cmp > 0 then (sn := unfold !sn; 0)
      else begin
        let shortcut =
          match !tn, !sn, hints d1 with
          | App _, App _, Regular _ when d1 == d2 ->
            if not (failed_before c !tn !sn) then begin
              let l1 = match get_app_fn !tn with Const { ls; _ } -> ls | _ -> [] in
              let l2 = match get_app_fn !sn with Const { ls; _ } -> ls | _ -> [] in
              if is_def_eq_levels l1 l2 && is_def_eq_args c !tn !sn then true
              else (cache_failure c !tn !sn; false)
            end else false
          | _ -> false in
        if shortcut then 1
        else (tn := unfold !tn; sn := unfold !sn; 0)
      end in
  if res <> 0 then res
  else match quick_is_def_eq c !tn !sn with
    | 1 -> 1
    | 0 -> 2
    | _ -> 0

and is_nat_zero t = match t with
  | NatLit { n; _ } -> Z.equal n Z.zero
  | Const { n; ls = []; _ } -> Name.equal n N.nat_zero
  | _ -> false

and is_nat_succ t = match t with
  | NatLit { n; _ } when not (Z.equal n Z.zero) -> Some (natlit (Z.pred n))
  | App { f = Const { n; ls = []; _ }; a; _ } when Name.equal n N.nat_succ -> Some a
  | _ -> None

and is_def_eq_offset c t s =
  if not c.bi.nat_ok then -1
  else if is_nat_zero t && is_nat_zero s then 1
  else match is_nat_succ t, is_nat_succ s with
    | Some a, Some b -> if is_def_eq_core c a b then 1 else 0
    | _ -> -1

and lazy_delta_reduction c tn sn =
  let rec loop () =
    let r = is_def_eq_offset c !tn !sn in
    if r <> -1 then r else begin
      let try_nat =
        if (not (has_fvar !tn) && not (has_fvar !sn)) || c.eager then begin
          match reduce_nat c !tn with
          | Some tv -> Some (if is_def_eq_core c tv !sn then 1 else 0)
          | None -> match reduce_nat c !sn with
            | Some sv -> Some (if is_def_eq_core c !tn sv then 1 else 0)
            | None -> None
        end else None in
      match try_nat with
      | Some r -> r
      | None ->
        match lazy_delta_reduction_step c tn sn with
        | 0 -> loop ()
        | 1 -> 1
        | 2 -> 0
        | _ -> -1
    end in
  loop ()

and lazy_delta_proj_reduction c tn sn sname idx =
  let rec loop () =
    match lazy_delta_reduction_step c tn sn with
    | 0 -> loop ()
    | 1 -> true
    | _ ->
      (match reduce_proj_core c !tn sname idx with
       | Some t -> (match reduce_proj_core c !sn sname idx with
           | Some s -> is_def_eq_core c t s
           | None -> is_def_eq_core c !tn !sn)
       | None -> is_def_eq_core c !tn !sn) in
  loop ()

and try_string_lit_expansion_core c t s =
  match t, s with
  | StrLit { s = str; _ }, App { f = Const { n; _ }; _ } when Name.equal n N.string_of_list && c.bi.str_ok ->
    if is_def_eq_core c (whnf c (string_lit_to_constructor str)) s then 1 else 0
  | _ -> -1

and try_string_lit_expansion c t s =
  let r = try_string_lit_expansion_core c t s in
  if r <> -1 then r else try_string_lit_expansion_core c s t

and is_def_eq_unit_like c t s =
  let t_type = whnf c (infer c t) in
  match get_app_fn t_type with
  | Const { n; _ } when is_non_rec_structure c n ->
    (match ind_info c n with
     | Some { ctors = [ctor]; _ } ->
       (match find c ctor with
        | Some { kind = Ctor { nfields = 0; _ }; _ } -> is_def_eq_core c t_type (infer c s)
        | _ -> false)
     | _ -> false)
  | _ -> false

and is_def_eq_core c t s =
  let r = quick_is_def_eq c t s in
  if r <> -1 then r = 1 else begin
    if (not (has_fvar t) || c.eager)
    && (match s with Const { n; _ } -> Name.equal n N.bool_true | _ -> false)
    && (match whnf c t with Const { n; _ } -> Name.equal n N.bool_true | _ -> false)
    then true
    else begin
      let tn = whnf_core ~cheap_proj:true c t and sn = whnf_core ~cheap_proj:true c s in
      let r = if tn != t || sn != s then quick_is_def_eq c tn sn else -1 in
      if r <> -1 then r = 1 else begin
        let r = is_def_eq_proof_irrel c tn sn in
        if r <> -1 then r = 1 else begin
          let tn = ref tn and sn = ref sn in
          let r = lazy_delta_reduction c tn sn in
          if r <> -1 then r = 1 else begin
            let tn = !tn and sn = !sn in
            match tn, sn with
            | Const { n = n1; ls = l1; _ }, Const { n = n2; ls = l2; _ }
              when Name.equal n1 n2 && is_def_eq_levels l1 l2 -> true
            | FVar { id = a; _ }, FVar { id = b; _ } when a = b -> true
            | _ ->
              let proj_ok = match tn, sn with
                | Proj { s = s1; idx = i1; e = e1; _ }, Proj { s = s2; idx = i2; e = e2; _ }
                  when Name.equal s1 s2 && i1 = i2 ->
                  lazy_delta_proj_reduction c (ref e1) (ref e2) s1 i1
                | _ -> false in
              if proj_ok then true else begin
                let tnn = whnf_core c tn and snn = whnf_core c sn in
                if tnn != tn || snn != sn then is_def_eq_core c tnn snn
                else if is_def_eq_app c tn sn then true
                else if try_eta_expansion c tn sn then true
                else if try_eta_struct c tn sn then true
                else begin
                  let r = try_string_lit_expansion c tn sn in
                  if r <> -1 then r = 1
                  else is_def_eq_unit_like c tn sn
                end
              end
          end
        end
      end
    end
  end

and is_def_eq c t s =
  let r = is_def_eq_core c t s in
  if r then cache_success c t s;
  r
