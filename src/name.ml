(* Hierarchical names, hash-consed. *)
type t =
  | Anon
  | Str of { h : int; pre : t; s : string }
  | Num of { h : int; pre : t; n : int }

let hash = function Anon -> 17 | Str { h; _ } -> h | Num { h; _ } -> h

module H = Hc.Make (struct
    type nonrec t = t
    let equal a b = match a, b with
      | Anon, Anon -> true
      | Str a, Str b -> a.pre == b.pre && String.equal a.s b.s
      | Num a, Num b -> a.pre == b.pre && a.n = b.n
      | _ -> false
    let hash = hash
    let dummy = Anon
  end)

let str pre s = H.intern (Str { h = Hc.mix (hash pre) (Hashtbl.hash s); pre; s })
let num pre n = H.intern (Num { h = Hc.mix (hash pre + 7) n; pre; n })

let of_list l = List.fold_left str Anon l
let of_string s = of_list (String.split_on_char '.' s)

let rec to_string = function
  | Anon -> "[anonymous]"
  | Str { pre = Anon; s; _ } -> s
  | Num { pre = Anon; n; _ } -> string_of_int n
  | Str { pre; s; _ } -> to_string pre ^ "." ^ s
  | Num { pre; n; _ } -> to_string pre ^ "." ^ string_of_int n

(* Structural equality; [==] suffices for interned names within a domain but this
   is robust across tiers. *)
let rec equal a b = a == b || match a, b with
  | Str x, Str y -> x.h = y.h && String.equal x.s y.s && equal x.pre y.pre
  | Num x, Num y -> x.h = y.h && x.n = y.n && equal x.pre y.pre
  | _ -> false

(* Total order (used by level normalisation). *)
let rec compare a b =
  if a == b then 0 else match a, b with
    | Anon, Anon -> 0
    | Anon, _ -> -1 | _, Anon -> 1
    | Num x, Num y -> let c = compare x.pre y.pre in if c <> 0 then c else Int.compare x.n y.n
    | Num _, Str _ -> -1 | Str _, Num _ -> 1
    | Str x, Str y -> let c = compare x.pre y.pre in if c <> 0 then c else String.compare x.s y.s

let rec is_prefix_of p n = equal p n || match n with
  | Anon -> false
  | Str { pre; _ } | Num { pre; _ } -> is_prefix_of p pre

(* replace_prefix n p p' : if p is a prefix of n, swap it for p' *)
let rec replace_prefix n p p' =
  if equal n p then p' else match n with
    | Anon -> Anon
    | Str { pre; s; _ } -> str (replace_prefix pre p p') s
    | Num { pre; n; _ } -> num (replace_prefix pre p p') n

(* Lean's Name.appendAfter: `a.b` ++ "_1" -> `a.b_1` *)
let append_after n suffix = match n with
  | Str { pre; s; _ } -> str pre (s ^ suffix)
  | _ -> str n suffix

let append_index_after n i = match n with
  | Str { pre; s; _ } -> str pre (s ^ "_" ^ string_of_int i)
  | _ -> str n ("_" ^ string_of_int i)

let rec append a b = match b with
  | Anon -> a
  | Str { pre; s; _ } -> str (append a pre) s
  | Num { pre; n; _ } -> num (append a pre) n

module Tbl = Hashtbl.Make (struct
    type nonrec t = t
    let equal = equal
    let hash = hash
  end)
