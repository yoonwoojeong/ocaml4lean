(* Names, universe levels and terms of the reference checker.

   Design rule: obviously correct beats fast.  Terms are plain trees (no
   hash-consing, no caching, no packed metadata).  Bound variables are de
   Bruijn indices; the checker only ever works on terms whose substituted
   values are closed (locally nameless: binders are opened with fresh free
   variables), so substitution needs no lifting. *)

(* ------------------------------------------------------------------ names *)
type comp = S of string | N of int
type name = comp list                      (* root first: Nat.add = [S "Nat"; S "add"] *)

let name_to_string (n : name) =
  if n = [] then "[anonymous]"
  else String.concat "." (List.map (function S s -> s | N i -> string_of_int i) n)

let name_of_string (s : string) : name = List.map (fun x -> S x) (String.split_on_char '.' s)

(* ----------------------------------------------------------------- levels *)
type level =
  | Zero
  | Succ of level
  | Max of level * level
  | IMax of level * level
  | Param of name

exception Too_complex of string

let rec level_params acc = function
  | Zero -> acc
  | Succ l -> level_params acc l
  | Max (a, b) | IMax (a, b) -> level_params (level_params acc a) b
  | Param n -> if List.mem n acc then acc else n :: acc

let rec level_succs = function
  | Zero | Param _ -> 0
  | Succ l -> 1 + level_succs l
  | Max (a, b) | IMax (a, b) -> level_succs a + level_succs b

let rec eval_level (sigma : (name * int) list) = function
  | Zero -> 0
  | Succ l -> 1 + eval_level sigma l
  | Max (a, b) -> max (eval_level sigma a) (eval_level sigma b)
  | IMax (a, b) -> let vb = eval_level sigma b in if vb = 0 then 0 else max (eval_level sigma a) vb
  | Param n -> List.assoc n sigma

(* Semantic level relations: "for every assignment of the parameters to
   natural numbers".  Decided by enumeration.  Why a bounded enumeration is
   exhaustive: a level is built from 0, +1, max, imax, so under an assignment
   it is a max of terms [p + k] (k <= c, c = number of succ nodes) or of
   constants, with imax only deciding whether a branch is 0.  Whether two such
   expressions are equal, or one is >= the other, depends only on the order of
   the parameter values and of 0 with differences capped at c+1: a gap larger
   than c+1 between consecutive values can be shrunk to c+1 without changing
   any comparison.  So values 0 .. n*(c+1) cover every case (n parameters). *)
let for_all_assignments (ls : level list) (p : (name * int) list -> bool) : bool =
  let ps = List.fold_left level_params [] ls in
  let n = List.length ps in
  let c = List.fold_left (fun a l -> a + level_succs l) 0 ls in
  let bound = n * (c + 1) in
  let total = ref 1.0 in
  for _ = 1 to n do total := !total *. float (bound + 1) done;
  if !total > 4e6 then raise (Too_complex "too many universe parameters for the reference level check");
  let rec go ps acc = match ps with
    | [] -> p acc
    | x :: rest ->
      let ok = ref true and v = ref 0 in
      while !ok && !v <= bound do
        if not (go rest ((x, !v) :: acc)) then ok := false;
        incr v
      done;
      !ok in
  go ps []

let level_equiv a b = a = b || for_all_assignments [a; b] (fun s -> eval_level s a = eval_level s b)
let level_geq a b = for_all_assignments [a; b] (fun s -> eval_level s a >= eval_level s b)
let level_is_zero a = a = Zero || for_all_assignments [a] (fun s -> eval_level s a = 0)
let level_never_zero a = for_all_assignments [a] (fun s -> eval_level s a >= 1)

let rec level_subst (ps : name list) (ls : level list) = function
  | Zero -> Zero
  | Succ l -> Succ (level_subst ps ls l)
  | Max (a, b) -> Max (level_subst ps ls a, level_subst ps ls b)
  | IMax (a, b) -> IMax (level_subst ps ls a, level_subst ps ls b)
  | Param n ->
    let rec find ps ls = match ps, ls with
      | p :: pr, l :: lr -> if p = n then l else find pr lr
      | _ -> Param n in
    find ps ls

let rec level_to_string = function
  | Zero -> "0"
  | Succ l -> level_to_string l ^ "+1"
  | Max (a, b) -> "max(" ^ level_to_string a ^ "," ^ level_to_string b ^ ")"
  | IMax (a, b) -> "imax(" ^ level_to_string a ^ "," ^ level_to_string b ^ ")"
  | Param n -> name_to_string n

(* ------------------------------------------------------------------ terms *)
type term =
  | Bvar of int
  | Fvar of int
  | Sort of level
  | Const of name * level list
  | App of term * term
  | Lam of term * term                      (* binder type, body *)
  | Pi of term * term
  | Let of term * term * term               (* type, value, body *)
  | Proj of name * int * term               (* structure name, field index, value *)
  | Nat of Rbig.t
  | Str of string

(* free variables: id -> type (the checker's local context) *)
let fvar_types : (int, term) Hashtbl.t = Hashtbl.create 64
let fvar_counter = ref 0
let fresh_fvar (ty : term) : term =
  incr fvar_counter;
  Hashtbl.replace fvar_types !fvar_counter ty;
  Fvar !fvar_counter
let fvar_type id = Hashtbl.find fvar_types id

(* does the term have a loose bound variable with index >= k? *)
let rec has_loose k = function
  | Bvar i -> i >= k
  | Fvar _ | Sort _ | Const _ | Nat _ | Str _ -> false
  | App (f, a) -> has_loose k f || has_loose k a
  | Lam (t, b) | Pi (t, b) -> has_loose k t || has_loose (k + 1) b
  | Let (t, v, b) -> has_loose k t || has_loose k v || has_loose (k + 1) b
  | Proj (_, _, e) -> has_loose k e
let closed t = not (has_loose 0 t)

(* [subst k v t]: replace bound variable k by v and lower the ones above.
   [v] must be closed (no loose bound variables), so it is never shifted. *)
let rec subst k v = function
  | Bvar i -> if i = k then v else if i > k then Bvar (i - 1) else Bvar i
  | (Fvar _ | Sort _ | Const _ | Nat _ | Str _) as t -> t
  | App (f, a) -> App (subst k v f, subst k v a)
  | Lam (t, b) -> Lam (subst k v t, subst (k + 1) v b)
  | Pi (t, b) -> Pi (subst k v t, subst (k + 1) v b)
  | Let (t, x, b) -> Let (subst k v t, subst k v x, subst (k + 1) v b)
  | Proj (s, i, e) -> Proj (s, i, subst k v e)

let instantiate1 body v = subst 0 v body

(* replace free variable [id] by bound variable index [k] (+ binder depth) *)
let rec abstract_fvar id k = function
  | Fvar j when j = id -> Bvar k
  | (Bvar _ | Fvar _ | Sort _ | Const _ | Nat _ | Str _) as t -> t
  | App (f, a) -> App (abstract_fvar id k f, abstract_fvar id k a)
  | Lam (t, b) -> Lam (abstract_fvar id k t, abstract_fvar id (k + 1) b)
  | Pi (t, b) -> Pi (abstract_fvar id k t, abstract_fvar id (k + 1) b)
  | Let (t, x, b) -> Let (abstract_fvar id k t, abstract_fvar id k x, abstract_fvar id (k + 1) b)
  | Proj (s, i, e) -> Proj (s, i, abstract_fvar id k e)

(* Π/λ over the free variables [xs] (outermost first) around [body]; the
   binder types are abstracted over the earlier variables. *)
let bind mk (xs : term list) (body : term) : term =
  (* the binder type of a later variable may mention an earlier one; it sits
     directly under the earlier binder, so abstracting at index 0 covers it *)
  let rec build xs = match xs with
    | [] -> body
    | (Fvar id) :: rest ->
      let inner = build rest in
      mk (fvar_type id) (abstract_fvar id 0 inner)
    | _ -> invalid_arg "Rterm.bind" in
  build xs
let mk_pi xs body = bind (fun t b -> Pi (t, b)) xs body
let mk_lam xs body = bind (fun t b -> Lam (t, b)) xs body

let rec subst_levels (ps : name list) (ls : level list) = function
  | Sort l -> Sort (level_subst ps ls l)
  | Const (n, us) -> Const (n, List.map (level_subst ps ls) us)
  | (Bvar _ | Fvar _ | Nat _ | Str _) as t -> t
  | App (f, a) -> App (subst_levels ps ls f, subst_levels ps ls a)
  | Lam (t, b) -> Lam (subst_levels ps ls t, subst_levels ps ls b)
  | Pi (t, b) -> Pi (subst_levels ps ls t, subst_levels ps ls b)
  | Let (t, v, b) -> Let (subst_levels ps ls t, subst_levels ps ls v, subst_levels ps ls b)
  | Proj (s, i, e) -> Proj (s, i, subst_levels ps ls e)

let rec app_fn = function App (f, _) -> app_fn f | t -> t
let app_args t =
  let rec go t acc = match t with App (f, a) -> go f (a :: acc) | _ -> acc in
  go t []
let mk_app f args = List.fold_left (fun f a -> App (f, a)) f args

(* structural equality up to equivalent universe levels *)
let rec term_eq a b =
  match a, b with
  | Sort l1, Sort l2 -> level_equiv l1 l2
  | Const (n1, u1), Const (n2, u2) ->
    n1 = n2 && List.length u1 = List.length u2 && List.for_all2 level_equiv u1 u2
  | App (f1, a1), App (f2, a2) -> term_eq f1 f2 && term_eq a1 a2
  | Lam (t1, b1), Lam (t2, b2) | Pi (t1, b1), Pi (t2, b2) -> term_eq t1 t2 && term_eq b1 b2
  | Let (t1, v1, b1), Let (t2, v2, b2) -> term_eq t1 t2 && term_eq v1 v2 && term_eq b1 b2
  | Proj (s1, i1, e1), Proj (s2, i2, e2) -> s1 = s2 && i1 = i2 && term_eq e1 e2
  | Nat x, Nat y -> Rbig.equal x y
  | Bvar i, Bvar j -> i = j
  | Fvar i, Fvar j -> i = j
  | Str s, Str t -> s = t
  | _ -> false

(* does some subterm satisfy p? *)
let rec exists p t =
  p t ||
  (match t with
   | App (f, a) -> exists p f || exists p a
   | Lam (x, b) | Pi (x, b) -> exists p x || exists p b
   | Let (x, v, b) -> exists p x || exists p v || exists p b
   | Proj (_, _, e) -> exists p e
   | _ -> false)

let rec to_string ?(depth = 6) t =
  if depth = 0 then "…" else
  let s = to_string ~depth:(depth - 1) in
  match t with
  | Bvar i -> "#" ^ string_of_int i
  | Fvar i -> "x" ^ string_of_int i
  | Sort l -> "Sort(" ^ level_to_string l ^ ")"
  | Const (n, us) -> name_to_string n ^ (if us = [] then "" else ".{" ^ String.concat "," (List.map level_to_string us) ^ "}")
  | App (f, a) -> "(" ^ s f ^ " " ^ s a ^ ")"
  | Lam (t, b) -> "(fun " ^ s t ^ " => " ^ s b ^ ")"
  | Pi (t, b) -> "(" ^ s t ^ " -> " ^ s b ^ ")"
  | Let (t, v, b) -> "(let " ^ s t ^ " := " ^ s v ^ "; " ^ s b ^ ")"
  | Proj (n, i, e) -> s e ^ "." ^ string_of_int i
  | Nat n -> Rbig.to_string n
  | Str x -> "\"" ^ String.escaped x ^ "\""
