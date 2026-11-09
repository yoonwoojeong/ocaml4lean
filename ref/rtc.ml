(* The reference type checker: environment, inference, reduction, definitional
   equality.  It follows the typing and conversion rules of Lean 4 (docs/DESIGN.md
   sections 5 and 6.1) and nothing else: no performance heuristics.  Differences
   from the production checker, on purpose:
   - everything is always fully checked (no "infer only" mode);
   - free variables never carry values (let is substituted);
   - no flags such as "eager reduce"; literal arithmetic is applied whenever the
     arguments reduce to literals, even under free variables;
   - universe levels are compared semantically (rterm.ml);
   - the only caches are exact memo tables keyed by whole terms. *)
open Rterm

exception Reject of string
let fail fmt = Printf.ksprintf (fun s -> raise (Reject s)) fmt

type hints = HOpaque | HAbbrev | HRegular of int
type safety = Safe | Unsafe | Partial

type ind = { nparams : int; nindices : int; all : name list; ctors : name list;
             nnested : int; is_rec : bool; is_reflexive : bool }
type ctor = { induct : name; cidx : int; cnparams : int; nfields : int }
type rule = { r_ctor : name; r_nfields : int; r_rhs : term }
type recr = { rall : name list; rnparams : int; rnindices : int; nmotives : int;
              nminors : int; rules : rule list; k : bool }
type quotk = QType | QCtor | QLift | QInd

type kind =
  | Axiom
  | Defn of { value : term; hints : hints; safety : safety; all : name list }
  | Thm of { value : term }
  | Opaq of { value : term }
  | Quot of quotk
  | Induct of ind
  | Ctor of ctor
  | Rec of recr

type decl = { name : name; lparams : name list; ty : term; kind : kind; unsafe : bool }

(* ------------------------------------------------------------ environment *)
let env : (name, decl) Hashtbl.t = Hashtbl.create 1024
let env_version = ref 0

(* the checking context: universe parameters in scope (None = do not check)
   and the safety level of the declaration being checked *)
let cur_lps : name list option ref = ref None
let cur_safety = ref Safe

module TH = Hashtbl.Make (struct
    type t = term
    let equal (a : term) (b : term) = a = b
    let hash (t : term) = Hashtbl.hash_param 30 200 t
  end)
module PH = Hashtbl.Make (struct
    type t = term * term
    let equal ((a, b) : t) ((c, d) : t) = a = c && b = d
    let hash ((a, b) : t) = Hashtbl.hash_param 30 200 a * 31 + Hashtbl.hash_param 30 200 b
  end)

let infer_cache : term TH.t = TH.create 1024
let whnf_cache : term TH.t = TH.create 1024
let eq_cache : bool PH.t = PH.create 1024
let clear_caches () = TH.reset infer_cache; TH.reset whnf_cache; PH.reset eq_cache

let set_context lps safety =
  cur_lps := lps; cur_safety := safety; clear_caches ()

let add_decl (d : decl) =
  if Hashtbl.mem env d.name then fail "duplicate declaration '%s'" (name_to_string d.name);
  Hashtbl.replace env d.name d;
  incr env_version;
  clear_caches ()

let remove_decl n =
  Hashtbl.remove env n; incr env_version; clear_caches ()

let find n = Hashtbl.find_opt env n
let get n = match find n with Some d -> d | None -> fail "unknown constant '%s'" (name_to_string n)

(* ------------------------------------------------------------ known names *)
let n_ = name_of_string
let nat_n = n_ "Nat" and nat_zero_n = n_ "Nat.zero" and nat_succ_n = n_ "Nat.succ"
let bool_n = n_ "Bool" and true_n = n_ "Bool.true" and false_n = n_ "Bool.false"
let string_n = n_ "String" and str_of_list_n = n_ "String.ofList"
let char_n = n_ "Char" and char_of_nat_n = n_ "Char.ofNat"
let list_n = n_ "List" and nil_n = n_ "List.nil" and cons_n = n_ "List.cons"
let nat_c = Const (nat_n, []) and bool_c = Const (bool_n, [])
let prop = Sort Zero

(* The Nat / String literal rules are sound only if these names denote the
   expected declarations.  Recomputed whenever the environment changed. *)
let builtins_version = ref (-1)
let nat_ok_v = ref false and str_ok_v = ref false
let nat_ops = [ "Nat.add", false; "Nat.sub", false; "Nat.mul", false; "Nat.pow", false; "Nat.gcd", false;
                "Nat.mod", false; "Nat.div", false; "Nat.beq", true; "Nat.ble", true; "Nat.land", false;
                "Nat.lor", false; "Nat.xor", false; "Nat.shiftLeft", false; "Nat.shiftRight", false ]
let compute_builtins () =
  let ty_is n lps ty = match find (n_ n) with
    | Some d -> d.lparams = lps && d.ty = ty && not d.unsafe
    | None -> false in
  let ind_is n nl ty ctors = match find (n_ n) with
    | Some ({ kind = Induct iv; _ } as d) ->
      List.length d.lparams = nl && d.ty = ty && iv.ctors = List.map n_ ctors && not d.unsafe
    | _ -> false in
  let bool_ok = ind_is "Bool" 0 (Sort (Succ Zero)) ["Bool.false"; "Bool.true"]
                && ty_is "Bool.false" [] bool_c && ty_is "Bool.true" [] bool_c in
  let nat_ok =
    ind_is "Nat" 0 (Sort (Succ Zero)) ["Nat.zero"; "Nat.succ"]
    && ty_is "Nat.zero" [] nat_c && ty_is "Nat.succ" [] (Pi (nat_c, nat_c))
    && List.for_all (fun (n, is_bool) ->
        match find (n_ n) with
        | None -> true
        | Some _ -> ty_is n [] (Pi (nat_c, Pi (nat_c, if is_bool then bool_c else nat_c))) && (not is_bool || bool_ok))
      nat_ops in
  let char_c = Const (char_n, []) in
  let list_char = App (Const (list_n, [Zero]), char_c) in
  let str_ok =
    nat_ok && ty_is "String.ofList" [] (Pi (list_char, Const (string_n, [])))
    && ty_is "Char.ofNat" [] (Pi (nat_c, char_c))
    && (match find list_n with
        | Some ({ kind = Induct { ctors; nparams = 1; nindices = 0; _ }; lparams = [_]; _ }) ->
          ctors = [nil_n; cons_n]
        | _ -> false) in
  nat_ok_v := nat_ok; str_ok_v := str_ok; builtins_version := !env_version
let nat_ok () = if !builtins_version <> !env_version then compute_builtins (); !nat_ok_v
let str_ok () = if !builtins_version <> !env_version then compute_builtins (); !str_ok_v

(* ------------------------------------------------------------------ misc *)
let check_level l =
  match !cur_lps with
  | None -> ()
  | Some ps ->
    List.iter (fun p -> if not (List.mem p ps) then
                  fail "undefined universe parameter '%s'" (name_to_string p))
      (level_params [] l)

let is_structure_like n = match find n with
  | Some { kind = Induct { ctors = [_]; nindices = 0; is_rec = false; _ }; _ } -> true
  | _ -> false

(* UTF-8 decoding for string literals *)
let utf8_decode s =
  let n = String.length s in
  let res = ref [] and i = ref 0 in
  while !i < n do
    let c = Char.code s.[!i] in
    let len, init =
      if c < 0x80 then 1, c else if c < 0xE0 then 2, c land 0x1F
      else if c < 0xF0 then 3, c land 0x0F else 4, c land 0x07 in
    let v = ref init in
    for k = 1 to len - 1 do
      if !i + k < n then v := (!v lsl 6) lor (Char.code s.[!i + k] land 0x3F)
    done;
    res := !v :: !res; i := !i + len
  done;
  List.rev !res

let string_to_ctor s =
  let char_c = Const (char_n, []) in
  let cons = App (Const (cons_n, [Zero]), char_c) and nil = App (Const (nil_n, [Zero]), char_c) in
  let l = List.fold_right (fun cp acc ->
      App (App (cons, App (Const (char_of_nat_n, []), Nat (Rbig.of_int cp))), acc)) (utf8_decode s) nil in
  App (Const (str_of_list_n, []), l)

let nat_to_ctor n =
  if Rbig.is_zero n then Const (nat_zero_n, [])
  else App (Const (nat_succ_n, []), Nat (Rbig.pred n))

(* ------------------------------------------------------------------ main *)
let max_shift = 1 lsl 24

let rec infer (t : term) : term =
  match TH.find_opt infer_cache t with
  | Some r -> r
  | None ->
    let r = infer_core t in
    TH.replace infer_cache t r; r

and infer_core t =
  match t with
  | Bvar _ -> fail "loose bound variable"
  | Fvar id -> fvar_type id
  | Sort l -> check_level l; Sort (Succ l)
  | Const (n, ls) ->
    let d = get n in
    if List.length d.lparams <> List.length ls then fail "wrong number of universe levels for '%s'" (name_to_string n);
    if d.unsafe && !cur_safety <> Unsafe then fail "safe declaration uses unsafe '%s'" (name_to_string n);
    (match d.kind with
     | Defn { safety = Partial; _ } when !cur_safety = Safe -> fail "safe declaration uses partial '%s'" (name_to_string n)
     | _ -> ());
    List.iter check_level ls;
    subst_levels d.lparams ls d.ty
  | App (f, a) ->
    (match whnf (infer f) with
     | Pi (dom, body) ->
       let ta = infer a in
       if not (is_def_eq ta dom) then
         fail "application type mismatch: %s : %s, expected %s" (to_string a) (to_string ta) (to_string dom);
       instantiate1 body a
     | _ -> fail "function expected: %s" (to_string f))
  | Lam (ty, b) ->
    ignore (ensure_sort (infer ty));
    let x = fresh_fvar ty in
    mk_pi [x] (infer (instantiate1 b x))
  | Pi (ty, b) ->
    let u = ensure_sort (infer ty) in
    let x = fresh_fvar ty in
    let v = ensure_sort (infer (instantiate1 b x)) in
    Sort (IMax (u, v))
  | Let (ty, v, b) ->
    ignore (ensure_sort (infer ty));
    if not (is_def_eq (infer v) ty) then fail "let value has the wrong type";
    infer (instantiate1 b v)
  | Proj (sname, idx, e) -> infer_proj sname idx e
  | Nat _ -> if find nat_n = None then fail "Nat literal but Nat is not declared"; nat_c
  | Str _ -> if find string_n = None then fail "String literal but String is not declared"; Const (string_n, [])

and ensure_sort t = match whnf t with Sort l -> l | _ -> fail "type expected: %s" (to_string t)

and is_prop_term e = (* is e a proposition, i.e. e : Prop ?  The type of e must reduce to a sort:
                         a stuck sort is an error, not "no" (Lean PR 14807, bugs/proj-of-subst-prop) *)
  level_is_zero (ensure_sort (infer e))

and infer_proj sname idx e =
  let bad () = fail "invalid projection %s" (to_string (Proj (sname, idx, e))) in
  let ty = whnf (infer e) in
  let head = app_fn ty and args = app_args ty in
  let iname, ilevels = match head with Const (n, ls) -> n, ls | _ -> bad () in
  if iname <> sname then bad ();
  let iv = match find iname with Some { kind = Induct iv; _ } -> iv | _ -> bad () in
  let cname = match iv.ctors with [c] -> c | _ -> bad () in
  if iv.nindices <> 0 || List.length args <> iv.nparams then bad ();
  let cd = get cname in
  if List.length cd.lparams <> List.length ilevels then bad ();
  let r = ref (subst_levels cd.lparams ilevels cd.ty) in
  List.iter (fun a -> match whnf !r with Pi (_, b) -> r := instantiate1 b a | _ -> bad ()) args;
  let prop_struct = is_prop_term ty in
  for i = 0 to idx - 1 do
    match whnf !r with
    | Pi (dom, b) ->
      if has_loose 0 b then begin
        if prop_struct && not (is_prop_term dom) then bad ();
        r := instantiate1 b (Proj (sname, i, e))
      end else r := b
    | _ -> bad ()
  done;
  match whnf !r with
  | Pi (dom, _) ->
    if prop_struct && not (is_prop_term dom) then bad ();
    dom
  | _ -> bad ()

(* ---------------------------------------------------------------- whnf *)
and beta f args =
  match f, args with
  | Lam (_, b), a :: rest -> beta (instantiate1 b a) rest
  | _ -> mk_app f args

and whnf_core (t : term) : term =
  match t with
  | App _ ->
    let f = app_fn t and args = app_args t in
    let f' = whnf_core f in
    (match f' with
     | Lam _ -> whnf_core (beta f' args)
     | _ ->
       let t' = if f' == f then t else mk_app f' args in
       (match reduce_rec t' with Some r -> whnf_core r | None -> t'))
  | Let (_, v, b) -> whnf_core (instantiate1 b v)
  | Proj (s, i, e) -> (match reduce_proj s i e with Some r -> whnf_core r | None -> t)
  | _ -> t

and whnf (t : term) : term =
  match t with
  | Sort _ | Pi _ | Lam _ | Nat _ | Str _ | Fvar _ | Bvar _ -> t
  | _ ->
    match TH.find_opt whnf_cache t with
    | Some r -> r
    | None ->
      let rec loop t =
        let t = whnf_core t in
        match reduce_nat t with
        | Some v -> v
        | None -> (match unfold t with Some t' -> loop t' | None -> t) in
      let r = loop t in
      TH.replace whnf_cache t r; r

and unfold t =
  match app_fn t with
  | Const (n, ls) ->
    (match find n with
     | Some { kind = (Defn { value; _ } | Thm { value }); lparams; _ } when List.length lparams = List.length ls ->
       Some (mk_app (subst_levels lparams ls value) (app_args t))
     | _ -> None)
  | _ -> None

and reduce_proj sname idx e =
  let e' = match whnf e with Str s when str_ok () -> whnf (string_to_ctor s) | x -> x in
  match app_fn e' with
  | Const (c, _) ->
    (match find c with
     | Some { kind = Ctor { induct; cnparams; _ }; _ } when induct = sname ->
       List.nth_opt (app_args e') (cnparams + idx)
     | _ -> None)
  | _ -> None

and reduce_rec t =
  match app_fn t with
  | Const (n, ls) ->
    (match find n with
     | Some ({ kind = Quot ((QLift | QInd) as q); _ }) -> reduce_quot q t
     | Some ({ kind = Rec r; _ } as d) -> reduce_iota d r ls t
     | _ -> None)
  | _ -> None

and reduce_quot q t =
  let args = Array.of_list (app_args t) in
  let mk_pos = (match q with QLift -> 5 | _ -> 4) and f_pos = 3 in
  if Array.length args <= mk_pos then None
  else begin
    let m = whnf args.(mk_pos) in
    match app_fn m, app_args m with
    | Const (c, _), [_; _; a] when (match find c with Some { kind = Quot QCtor; _ } -> true | _ -> false) ->
      let rest = Array.to_list (Array.sub args (mk_pos + 1) (Array.length args - mk_pos - 1)) in
      Some (mk_app (App (args.(f_pos), a)) rest)
    | _ -> None
  end

(* the inductive type of a recursor's major premise, read off the recursor's type *)
and major_inductive (d : decl) (r : recr) =
  let k = r.rnparams + r.nmotives + r.nminors + r.rnindices in
  let rec skip t k = match t with
    | Pi (dom, b) -> if k = 0 then (match app_fn dom with Const (n, _) -> Some n | _ -> None) else skip b (k - 1)
    | _ -> None in
  skip d.ty k

and reduce_iota (d : decl) (r : recr) ls t =
  let args = Array.of_list (app_args t) in
  let nargs = Array.length args in
  let major_idx = r.rnparams + r.nmotives + r.nminors + r.rnindices in
  if major_idx >= nargs then None
  else begin
    let induct = major_inductive d r in
    let major = args.(major_idx) in
    let major = if r.k then (match induct with Some i -> to_ctor_when_k i r major | None -> major) else major in
    let major = match whnf major with
      | Nat n when nat_ok () -> nat_to_ctor n
      | Str s when str_ok () -> whnf (string_to_ctor s)
      | m -> (match induct with Some i -> to_ctor_when_structure i m | None -> m) in
    match app_fn major with
    | Const (cn, _) ->
      (match List.find_opt (fun rl -> rl.r_ctor = cn) r.rules with
       | None -> None
       | Some rule ->
         let margs = Array.of_list (app_args major) in
         let nm = Array.length margs in
         if rule.r_nfields > nm || List.length ls <> List.length d.lparams then None
         else begin
           let rhs = subst_levels d.lparams ls rule.r_rhs in
           let pre = Array.to_list (Array.sub args 0 (r.rnparams + r.nmotives + r.nminors)) in
           let fields = Array.to_list (Array.sub margs (nm - rule.r_nfields) rule.r_nfields) in
           let rest = Array.to_list (Array.sub args (major_idx + 1) (nargs - major_idx - 1)) in
           Some (mk_app rhs (pre @ fields @ rest))
         end)
    | _ -> None
  end

(* K-like recursors: replace the major premise by the constructor application
   when its type is that inductive type and the types agree *)
and to_ctor_when_k induct r major =
  let ty = whnf (infer major) in
  match app_fn ty with
  | Const (n, ls) when n = induct ->
    (match find n with
     | Some { kind = Induct { ctors = ctor :: _; _ }; _ } ->
       let targs = app_args ty in
       if List.length targs < r.rnparams then major
       else begin
         let params = List.filteri (fun i _ -> i < r.rnparams) targs in
         let c = mk_app (Const (ctor, ls)) params in
         if is_def_eq ty (infer c) then c else major
       end
     | _ -> major)
  | _ -> major

(* structure eta for recursor reduction: s is replaced by mk (s.1) ... (s.n) *)
and to_ctor_when_structure induct e =
  if not (is_structure_like induct) then e
  else match app_fn e with
    | Const (c, _) when (match find c with Some { kind = Ctor _; _ } -> true | _ -> false) -> e
    | _ ->
      let ty = whnf (infer e) in
      (match app_fn ty with
       | Const (n, ls) when n = induct ->
         if is_prop_term ty then e
         else begin
           match find n with
           | Some { kind = Induct { ctors = [cn]; _ }; _ } ->
             (match find cn with
              | Some { kind = Ctor { cnparams; nfields; _ }; _ } ->
                let params = List.filteri (fun i _ -> i < cnparams) (app_args ty) in
                let c = mk_app (Const (cn, ls)) params in
                let fields = List.init nfields (fun i -> Proj (induct, i, e)) in
                mk_app c fields
              | _ -> e)
           | _ -> e
         end
       | _ -> e)

(* literal arithmetic *)
and nat_value t = match t with
  | Nat v -> Some v
  | Const (n, []) when n = nat_zero_n -> Some Rbig.zero
  | _ -> None

and reduce_nat t : term option =
  if not (nat_ok ()) then None else
  match t with
  | App (Const (n, []), a) when n = nat_succ_n ->
    (match nat_value (whnf a) with Some v -> Some (Nat (Rbig.succ v)) | None -> None)
  | App (App (Const (op, []), a), b) when List.mem_assoc (name_to_string op) nat_ops ->
    (match nat_value (whnf a) with
     | None -> None
     | Some x ->
       match nat_value (whnf b) with
       | None -> None
       | Some y ->
         let open Rbig in
         let lit v = Some (Nat v) and bl v = Some (Const ((if v then true_n else false_n), [])) in
         (match name_to_string op with
          | "Nat.add" -> lit (add x y)
          | "Nat.sub" -> lit (if compare x y <= 0 then zero else sub x y)
          | "Nat.mul" -> lit (mul x y)
          | "Nat.pow" -> (match to_int_opt y with Some k when k <= max_shift -> lit (pow x k) | _ -> None)
          | "Nat.gcd" -> lit (gcd x y)
          | "Nat.mod" -> lit (if is_zero y then x else snd (divmod x y))
          | "Nat.div" -> lit (if is_zero y then zero else fst (divmod x y))
          | "Nat.beq" -> bl (equal x y)
          | "Nat.ble" -> bl (compare x y <= 0)
          | "Nat.land" -> lit (logand x y)
          | "Nat.lor" -> lit (logor x y)
          | "Nat.xor" -> lit (logxor x y)
          | "Nat.shiftLeft" ->
            (match to_int_opt y with Some k when k <= max_shift -> lit (shift_left x k) | _ -> None)
          | "Nat.shiftRight" -> (match to_int_opt y with Some k -> lit (shift_right x k) | None -> lit zero)
          | _ -> None))
  | _ -> None

(* ------------------------------------------------- definitional equality *)
and is_def_eq (t : term) (s : term) : bool =
  if t = s then true
  else match PH.find_opt eq_cache (t, s) with
    | Some r -> r
    | None ->
      let r = is_def_eq_core t s in
      PH.replace eq_cache (t, s) r; r

and is_def_eq_core t s =
  let t = whnf_core t and s = whnf_core s in
  match quick t s with
  | Some b -> b
  | None ->
    match proof_irrel t s with
    | Some b -> b
    | None -> delta_loop t s

and quick t s : bool option =
  if term_eq t s then Some true
  else match t, s with
    | Lam (d1, b1), Lam (d2, b2) | Pi (d1, b1), Pi (d2, b2) ->
      if not (is_def_eq d1 d2) then Some false
      else begin
        let x = fresh_fvar d1 in
        Some (is_def_eq (instantiate1 b1 x) (instantiate1 b2 x))
      end
    | Sort l1, Sort l2 -> Some (level_equiv l1 l2)
    | Nat a, Nat b -> Some (Rbig.equal a b)
    | Str a, Str b -> Some (a = b)
    | _ -> None

and proof_irrel t s : bool option =
  let tt = infer t in
  if is_prop_term tt then Some (is_def_eq tt (infer s)) else None

and delta_info t =
  match app_fn t with
  | Const (n, ls) ->
    (match find n with
     | Some { kind = Defn { hints; _ }; lparams; _ } when List.length lparams = List.length ls -> Some (n, hints)
     | Some { kind = Thm _; lparams; _ } when List.length lparams = List.length ls -> Some (n, HOpaque)
     | _ -> None)
  | _ -> None

(* unfold priority: > 0 means the first should be unfolded first *)
and hint_cmp h1 h2 = match h1, h2 with
  | HRegular a, HRegular b -> compare a b
  | HAbbrev, HAbbrev | HOpaque, HOpaque -> 0
  | HAbbrev, _ -> 1
  | _, HAbbrev -> -1
  | HOpaque, _ -> -1
  | _, HOpaque -> 1

and nat_succ_pred t = match t with
  | Nat n when not (Rbig.is_zero n) -> Some (Nat (Rbig.pred n))
  | App (Const (n, []), a) when n = nat_succ_n -> Some a
  | _ -> None

and nat_is_zero t = match t with
  | Nat n -> Rbig.is_zero n
  | Const (n, []) when n = nat_zero_n -> true
  | _ -> false

and delta_loop t s : bool =
  match quick t s with
  | Some b -> b
  | None ->
    if nat_ok () && nat_is_zero t && nat_is_zero s then true
    else match (if nat_ok () then (nat_succ_pred t, nat_succ_pred s) else (None, None)) with
      | Some a, Some b -> is_def_eq a b
      | _ ->
        match reduce_nat t with
        | Some tv -> is_def_eq tv s
        | None ->
          match reduce_nat s with
          | Some sv -> is_def_eq t sv
          | None ->
            match delta_info t, delta_info s with
            | None, None -> structural t s
            | Some _, None -> delta_loop (whnf_core (unfold_exn t)) s
            | None, Some _ -> delta_loop t (whnf_core (unfold_exn s))
            | Some (n1, h1), Some (n2, h2) ->
              let c = hint_cmp h1 h2 in
              if c > 0 then delta_loop (whnf_core (unfold_exn t)) s
              else if c < 0 then delta_loop t (whnf_core (unfold_exn s))
              else begin
                let same_head =
                  n1 = n2 && (match app_fn t, app_fn s with
                      | Const (_, l1), Const (_, l2) -> List.length l1 = List.length l2 && List.for_all2 level_equiv l1 l2
                      | _ -> false) in
                let a1 = app_args t and a2 = app_args s in
                if same_head && List.length a1 = List.length a2 && List.for_all2 is_def_eq a1 a2 then true
                else delta_loop (whnf_core (unfold_exn t)) (whnf_core (unfold_exn s))
              end

and unfold_exn t = match unfold t with Some r -> r | None -> fail "internal: cannot unfold"

(* neither side can be unfolded or reduced further *)
and structural t s : bool =
  (match t, s with
   | Const (a, l1), Const (b, l2) ->
     a = b && List.length l1 = List.length l2 && List.for_all2 level_equiv l1 l2
   | Fvar i, Fvar j -> i = j
   | Proj (s1, i1, e1), Proj (s2, i2, e2) -> s1 = s2 && i1 = i2 && is_def_eq e1 e2
   | _ -> false)
  || def_eq_app t s
  || eta t s || eta s t
  || eta_struct t s || eta_struct s t
  || string_expansion t s || string_expansion s t
  || unit_like t s

and def_eq_app t s =
  match t, s with
  | App _, App _ ->
    let a1 = app_args t and a2 = app_args s in
    List.length a1 = List.length a2 && is_def_eq (app_fn t) (app_fn s) && List.for_all2 is_def_eq a1 a2
  | _ -> false

and eta t s =
  match t, s with
  | Lam _, Lam _ -> false
  | Lam _, _ ->
    (match whnf (infer s) with
     | Pi (dom, _) -> is_def_eq t (Lam (dom, App (s, Bvar 0)))
     | _ -> false)
  | _ -> false

(* t is a constructor application of a structure, s is not: compare field-wise *)
and eta_struct t s =
  match app_fn t with
  | Const (c, _) ->
    (match find c with
     | Some { kind = Ctor { induct; cnparams; nfields; _ }; _ }
       when List.length (app_args t) = cnparams + nfields && is_structure_like induct ->
       is_def_eq (infer t) (infer s)
       && List.for_all2 (fun i a -> is_def_eq (Proj (induct, i, s)) a)
         (List.init nfields (fun i -> i))
         (List.filteri (fun i _ -> i >= cnparams) (app_args t))
     | _ -> false)
  | _ -> false

and string_expansion t s =
  match t, s with
  | Str str, App (Const (n, _), _) when n = str_of_list_n && str_ok () -> is_def_eq (whnf (string_to_ctor str)) s
  | _ -> false

and unit_like t s =
  let ty = whnf (infer t) in
  match app_fn ty with
  | Const (n, _) when is_structure_like n ->
    (match find n with
     | Some { kind = Induct { ctors = [c]; _ }; _ } ->
       (match find c with
        | Some { kind = Ctor { nfields = 0; _ }; _ } -> is_def_eq ty (infer s)
        | _ -> false)
     | _ -> false)
  | _ -> false

(* ------------------------------------------------------------- public *)
let check_type_of (t : term) : term = infer t
