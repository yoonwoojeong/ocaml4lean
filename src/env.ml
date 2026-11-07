(* Constants of the environment, as read from the export file. *)
type hints = Opaque | Abbrev | Regular of int
type safety = Safe | Unsafe | Partial

type rule = { r_ctor : Name.t; r_nfields : int; r_rhs : Expr.t }

type quot_kind = QType | QCtor | QLift | QInd

type ind_val = { nparams : int; nindices : int; all : Name.t list; ctors : Name.t list;
                 nnested : int; is_rec : bool; is_reflexive : bool }
type ctor_val = { induct : Name.t; cidx : int; cnparams : int; nfields : int }
type rec_val = { rall : Name.t list; rnparams : int; rnindices : int; nmotives : int;
                 nminors : int; rules : rule list; k : bool }

type kind =
  | Axiom
  | Defn of { value : Expr.t; hints : hints; safety : safety; all : Name.t list }
  | Thm of { value : Expr.t; all : Name.t list }
  | Opaq of { value : Expr.t; all : Name.t list }
  | Quot of quot_kind
  | Induct of ind_val
  | Ctor of ctor_val
  | Recursor of rec_val

type cinfo = {
  name : Name.t;
  lparams : Name.t list;
  ty : Expr.t;
  kind : kind;
  unsafe : bool;
  mutable pos : int;          (* index of the declaration block introducing it *)
}

(* A unit of checking, in stream order. *)
type block =
  | Single of cinfo
  | QuotBlock of cinfo list
  | IndBlock of { types : cinfo list; ctors : cinfo list; recs : cinfo list }

type t = {
  consts : (Name.t, cinfo) Hashtbl.t;
  blocks : block array;
  dups : Name.t list;            (* names declared more than once *)
}

let has_value c = match c.kind with Defn _ | Thm _ -> true | _ -> false

let value c = match c.kind with
  | Defn { value; _ } | Thm { value; _ } | Opaq { value; _ } -> Some value
  | _ -> None

let hints c = match c.kind with
  | Defn { hints; _ } -> hints
  | _ -> Opaque

(* Lean's reducibility_hints compare: <0 means unfold t first *)
let compare_hints h1 h2 = match h1, h2 with
  | Regular a, Regular b -> if a = b then 0 else if a > b then -1 else 1
  | Opaque, Opaque | Abbrev, Abbrev -> 0
  | Opaque, _ -> 1
  | _, Opaque -> -1
  | Abbrev, _ -> -1
  | _, Abbrev -> 1

let block_names = function
  | Single c -> [c.name]
  | QuotBlock l -> List.map (fun c -> c.name) l
  | IndBlock { types; ctors; recs } -> List.map (fun c -> c.name) (types @ ctors @ recs)
