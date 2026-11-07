(* Universe levels, hash-consed.  Semantics follow Lean's kernel/level.cpp. *)
type t =
  | Zero
  | Succ of { h : int; l : t }
  | Max of { h : int; a : t; b : t }
  | IMax of { h : int; a : t; b : t }
  | Param of { h : int; n : Name.t }

let hash = function
  | Zero -> 11 | Succ { h; _ } | Max { h; _ } | IMax { h; _ } | Param { h; _ } -> h

module H = Hc.Make (struct
    type nonrec t = t
    let equal a b = match a, b with
      | Zero, Zero -> true
      | Succ x, Succ y -> x.l == y.l
      | Max x, Max y -> x.a == y.a && x.b == y.b
      | IMax x, IMax y -> x.a == y.a && x.b == y.b
      | Param x, Param y -> x.n == y.n
      | _ -> false
    let hash = hash
    let dummy = Zero
  end)

let zero = Zero
let succ l = H.intern (Succ { h = Hc.mix (hash l) 3; l })
let max_core a b = H.intern (Max { h = Hc.mix (Hc.mix (hash a) (hash b)) 5; a; b })
let imax_core a b = H.intern (IMax { h = Hc.mix (Hc.mix (hash a) (hash b)) 7; a; b })
let param n = H.intern (Param { h = Hc.mix (Name.hash n) 13; n })
let one = succ zero

(* structural equality, robust across hash-consing tiers *)
let rec equal a b = a == b || (hash a = hash b && match a, b with
  | Succ x, Succ y -> equal x.l y.l
  | Max x, Max y -> equal x.a y.a && equal x.b y.b
  | IMax x, IMax y -> equal x.a y.a && equal x.b y.b
  | Param x, Param y -> Name.equal x.n y.n
  | _ -> false)

let rec has_param = function
  | Zero -> false
  | Param _ -> true
  | Succ { l; _ } -> has_param l
  | Max { a; b; _ } | IMax { a; b; _ } -> has_param a || has_param b

let rec to_offset l k = match l with Succ { l; _ } -> to_offset l (k + 1) | _ -> (l, k)
let is_explicit l = match to_offset l 0 with (Zero, _) -> true | _ -> false
let depth l = snd (to_offset l 0)

let rec is_not_zero = function
  | Zero | Param _ -> false
  | Succ _ -> true
  | Max { a; b; _ } -> is_not_zero a || is_not_zero b
  | IMax { b; _ } -> is_not_zero b

let rec normalizes_to_zero = function
  | Zero -> true
  | Param _ | Succ _ -> false
  | Max { a; b; _ } -> normalizes_to_zero a && normalizes_to_zero b
  | IMax { b; _ } -> normalizes_to_zero b

let rec mk_succn l k = if k = 0 then l else mk_succn (succ l) (k - 1)

let mk_max a b =
  if is_explicit a && is_explicit b then (if depth a >= depth b then a else b)
  else if a == b then a
  else if a == Zero then b
  else if b == Zero then a
  else match a, b with
    | _, Max m when m.a == a || m.b == a -> b
    | Max m, _ when m.a == b || m.b == b -> a
    | _ ->
      let (p1, k1) = to_offset a 0 and (p2, k2) = to_offset b 0 in
      if p1 == p2 then (if k1 > k2 then a else b) else max_core a b

let mk_imax a b =
  if is_not_zero b then mk_max a b
  else if b == Zero then b
  else if a == Zero || a == one then b
  else if a == b then a
  else imax_core a b

(* total order for normalisation: kind of base, then base, then offset *)
let kind_rank = function Zero -> 0 | Succ _ -> 1 | Max _ -> 2 | IMax _ -> 3 | Param _ -> 4

let rec norm_cmp a b =
  if a == b then 0 else
    let (l1, k1) = to_offset a 0 and (l2, k2) = to_offset b 0 in
    if l1 != l2 then begin
      let r1 = kind_rank l1 and r2 = kind_rank l2 in
      if r1 <> r2 then compare r1 r2 else match l1, l2 with
        | Param x, Param y -> Name.compare x.n y.n
        | Max x, Max y -> if x.a != y.a then norm_cmp x.a y.a else norm_cmp x.b y.b
        | IMax x, IMax y -> if x.a != y.a then norm_cmp x.a y.a else norm_cmp x.b y.b
        | _ -> 0
    end else compare k1 k2

let rec push_max_args l acc = match l with
  | Max { a; b; _ } -> push_max_args b (push_max_args a acc)
  | _ -> l :: acc

let mk_max_list = function
  | [] -> assert false
  | l ->
    let rev = List.rev l in
    (match rev with
     | last :: rest -> List.fold_left (fun r a -> mk_max a r) last rest
     | [] -> assert false)

let rec normalize l =
  let (r, k) = to_offset l 0 in
  match r with
  | Succ _ -> assert false
  | Zero | Param _ -> l
  | IMax { a; b; _ } -> mk_succn (mk_imax (normalize a) (normalize b)) k
  | Max _ ->
    let todo = List.rev (push_max_args r []) in
    let args = List.fold_left (fun acc a -> push_max_args (normalize a) acc) [] todo in
    let args = Array.of_list (List.rev args) in
    Array.stable_sort norm_cmp args;
    let n = Array.length args in
    let i = ref 0 in
    if is_explicit args.(0) then begin
      while !i + 1 < n && is_explicit args.(!i + 1) do incr i done;
      let kk = depth args.(!i) in
      let j = ref (!i + 1) in
      while !j < n && snd (to_offset args.(!j) 0) < kk do incr j done;
      if !j < n then incr i
    end;
    let rargs = ref [args.(!i)] in
    let prev = ref (to_offset args.(!i) 0) in
    incr i;
    while !i < n do
      let cur = to_offset args.(!i) 0 in
      if fst !prev == fst cur then begin
        if snd !prev < snd cur then begin
          prev := cur; rargs := args.(!i) :: List.tl !rargs
        end
      end else begin
        prev := cur; rargs := args.(!i) :: !rargs
      end;
      incr i
    done;
    mk_max_list (List.rev_map (fun a -> mk_succn a k) !rargs)

let is_equiv a b = a == b || equal a b || equal (normalize a) (normalize b)

let rec is_geq_core l1 l2 =
  if l1 == l2 || l2 == Zero then true
  else match l1, l2 with
    | _, Max { a; b; _ } -> is_geq l1 a && is_geq l1 b
    | Max { a; b; _ }, _ when is_geq a l2 || is_geq b l2 -> true
    | _, IMax { a; b; _ } -> is_geq l1 a && is_geq l1 b
    | IMax { b; _ }, _ -> is_geq b l2
    | _ ->
      let (p1, k1) = to_offset l1 0 and (p2, k2) = to_offset l2 0 in
      if p1 == p2 || p2 == Zero then k1 >= k2
      else if k1 = k2 && k1 > 0 then is_geq p1 p2
      else false
and is_geq l1 l2 = is_geq_core (normalize l1) (normalize l2)

(* instantiate parameters *)
let rec instantiate (ps : Name.t list) (ls : t list) l =
  if not (has_param l) then l else match l with
    | Zero -> l
    | Succ { l = x; _ } -> succ (instantiate ps ls x)
    | Max { a; b; _ } -> mk_max (instantiate ps ls a) (instantiate ps ls b)
    | IMax { a; b; _ } -> mk_imax (instantiate ps ls a) (instantiate ps ls b)
    | Param { n; _ } ->
      let rec go ps ls = match ps, ls with
        | p :: ps, v :: ls -> if Name.equal p n then v else go ps ls
        | _ -> l in
      go ps ls

(* undefined parameter check *)
let rec undef_param (ps : Name.t list) = function
  | Zero -> None
  | Succ { l; _ } -> undef_param ps l
  | Max { a; b; _ } | IMax { a; b; _ } ->
    (match undef_param ps a with None -> undef_param ps b | r -> r)
  | Param { n; _ } -> if List.exists (Name.equal n) ps then None else Some n

let rec to_string l = match l with
  | Zero -> "0"
  | Succ _ when is_explicit l -> string_of_int (depth l)
  | Succ { l; _ } -> "(succ " ^ to_string l ^ ")"
  | Max { a; b; _ } -> "(max " ^ to_string a ^ " " ^ to_string b ^ ")"
  | IMax { a; b; _ } -> "(imax " ^ to_string a ^ " " ^ to_string b ^ ")"
  | Param { n; _ } -> Name.to_string n
