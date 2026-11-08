(* Arbitrary-precision natural numbers, for Nat literals.

   Replaces the subset of Zarith the checker used, so that the checker builds
   with nothing but the OCaml distribution.  Numbers are non-negative,
   little-endian arrays of base-2^28 limbs, normalised (no high zero limbs;
   zero is the empty array), and immutable.  Algorithms are the schoolbook ones;
   numbers in kernel workloads are small, and the official kernel bounds their
   size anyway (see [Tc.max_nat_bytes]).

   [sub a b] and [pred a] require [a >= b] / [a > 0]: the checker only calls
   them under that guard (truncated subtraction is done by the caller). *)

type t = int array

let bits = 28
let base = 1 lsl bits
let mask = base - 1

let norm (a : int array) : t =
  let n = ref (Array.length a) in
  while !n > 0 && a.(!n - 1) = 0 do decr n done;
  if !n = Array.length a then a else Array.sub a 0 !n

let zero : t = [||]
let one : t = [| 1 |]

let of_int (x : int) : t =
  if x < 0 then invalid_arg "Z.of_int: negative";
  let rec limbs x = if x = 0 then [] else (x land mask) :: limbs (x lsr bits) in
  Array.of_list (limbs x)

let sign (a : t) = if Array.length a = 0 then 0 else 1

let compare (a : t) (b : t) =
  let la = Array.length a and lb = Array.length b in
  if la <> lb then compare la lb
  else begin
    let r = ref 0 and i = ref (la - 1) in
    while !r = 0 && !i >= 0 do
      r := compare a.(!i) b.(!i); decr i
    done;
    !r
  end

let equal a b = compare a b = 0
let leq a b = compare a b <= 0
let gt a b = compare a b > 0

(* fits in a non-negative OCaml int? *)
let fits_int (a : t) = Array.length a <= 2 || (Array.length a = 3 && a.(2) < 1 lsl (62 - 2 * bits))

let to_int (a : t) =
  if not (fits_int a) then failwith "Z.to_int: overflow";
  let r = ref 0 in
  for i = Array.length a - 1 downto 0 do r := (!r lsl bits) lor a.(i) done;
  !r

let numbits (a : t) =
  let n = Array.length a in
  if n = 0 then 0
  else begin
    let top = a.(n - 1) in
    let b = ref 0 in
    while top lsr !b > 0 do incr b done;
    (n - 1) * bits + !b
  end

let hash (a : t) = Array.fold_left (fun h x -> (h * 1000003) lxor x) 17 a

let add (a : t) (b : t) : t =
  let a, b = if Array.length a >= Array.length b then a, b else b, a in
  let la = Array.length a and lb = Array.length b in
  let r = Array.make (la + 1) 0 in
  let c = ref 0 in
  for i = 0 to la - 1 do
    let s = a.(i) + (if i < lb then b.(i) else 0) + !c in
    r.(i) <- s land mask; c := s lsr bits
  done;
  r.(la) <- !c;
  norm r

let sub (a : t) (b : t) : t =
  if compare a b < 0 then invalid_arg "Z.sub: negative result";
  let la = Array.length a and lb = Array.length b in
  let r = Array.make la 0 in
  let br = ref 0 in
  for i = 0 to la - 1 do
    let d = a.(i) - (if i < lb then b.(i) else 0) - !br in
    if d < 0 then (r.(i) <- d + base; br := 1) else (r.(i) <- d; br := 0)
  done;
  norm r

let succ a = add a one
let pred a = sub a one

let mul (a : t) (b : t) : t =
  let la = Array.length a and lb = Array.length b in
  if la = 0 || lb = 0 then zero
  else begin
    let r = Array.make (la + lb) 0 in
    for i = 0 to la - 1 do
      let ai = a.(i) in
      if ai <> 0 then begin
        let c = ref 0 in
        for j = 0 to lb - 1 do
          (* ai * bj < 2^56, plus two values < 2^28: fits in 63 bits *)
          let s = r.(i + j) + ai * b.(j) + !c in
          r.(i + j) <- s land mask; c := s lsr bits
        done;
        let k = ref (i + lb) in
        while !c <> 0 do
          let s = r.(!k) + !c in
          r.(!k) <- s land mask; c := s lsr bits; incr k
        done
      end
    done;
    norm r
  end

let shift_left (a : t) (k : int) : t =
  if k < 0 then invalid_arg "Z.shift_left";
  if Array.length a = 0 then zero
  else begin
    let q = k / bits and s = k mod bits in
    let la = Array.length a in
    let r = Array.make (la + q + 1) 0 in
    for i = 0 to la - 1 do
      let v = a.(i) lsl s in
      r.(i + q) <- r.(i + q) lor (v land mask);
      r.(i + q + 1) <- v lsr bits
    done;
    norm r
  end

let shift_right (a : t) (k : int) : t =
  if k < 0 then invalid_arg "Z.shift_right";
  let q = k / bits and s = k mod bits in
  let la = Array.length a in
  if q >= la then zero
  else begin
    let r = Array.make (la - q) 0 in
    for i = 0 to la - q - 1 do
      let lo = a.(i + q) lsr s in
      let hi = if i + q + 1 < la then (a.(i + q + 1) lsl (bits - s)) land mask else 0 in
      r.(i) <- lo lor hi
    done;
    norm r
  end

(* division by a single limb d (0 < d < base): quotient and remainder *)
let divmod_small (a : t) (d : int) : t * int =
  let la = Array.length a in
  let q = Array.make la 0 in
  let r = ref 0 in
  for i = la - 1 downto 0 do
    let cur = (!r lsl bits) lor a.(i) in
    q.(i) <- cur / d; r := cur mod d
  done;
  (norm q, !r)

(* general division: binary long division on limbs *)
let divmod (a : t) (b : t) : t * t =
  if Array.length b = 0 then raise Division_by_zero;
  if compare a b < 0 then (zero, a)
  else if Array.length b = 1 then
    let q, r = divmod_small a b.(0) in (q, of_int r)
  else begin
    let n = numbits a and m = numbits b in
    let q = Array.make (Array.length a) 0 in
    (* bring down bits of a from the top; the remainder stays < 2b *)
    let r = ref (shift_right a (n - m + 1)) in
    for i = n - m downto 0 do
      let bit = (a.(i / bits) lsr (i mod bits)) land 1 in
      r := shift_left !r 1;
      if bit = 1 then r := add !r one;
      if compare !r b >= 0 then begin
        r := sub !r b;
        q.(i / bits) <- q.(i / bits) lor (1 lsl (i mod bits))
      end
    done;
    (norm q, !r)
  end

let div a b = fst (divmod a b)
let rem a b = snd (divmod a b)

let rec gcd a b = if Array.length b = 0 then a else gcd b (rem a b)

let pow (a : t) (k : int) : t =
  if k < 0 then invalid_arg "Z.pow";
  let rec go acc base k =
    if k = 0 then acc
    else go (if k land 1 = 1 then mul acc base else acc) (if k > 1 then mul base base else base) (k lsr 1) in
  go one a k

let bitwise f (a : t) (b : t) : t =
  let n = max (Array.length a) (Array.length b) in
  let get x i = if i < Array.length x then x.(i) else 0 in
  norm (Array.init n (fun i -> f (get a i) (get b i)))

let logand = bitwise ( land )
let logor = bitwise ( lor )
let logxor = bitwise ( lxor )

(* decimal conversion, 7 digits at a time (10^7 < 2^28) *)
let chunk = 10_000_000

let of_string (s : string) : t =
  let n = String.length s in
  if n = 0 then invalid_arg "Z.of_string";
  String.iter (fun c -> if c < '0' || c > '9' then invalid_arg "Z.of_string") s;
  let r = ref zero in
  let i = ref 0 in
  let first = n mod 7 in
  let take len =
    let v = int_of_string (String.sub s !i len) in
    i := !i + len;
    let p = ref 1 in for _ = 1 to len do p := !p * 10 done;
    r := add (mul !r (of_int !p)) (of_int v) in
  if first > 0 then take first;
  while !i < n do take 7 done;
  !r

let to_string (a : t) : string =
  if Array.length a = 0 then "0"
  else begin
    let parts = ref [] and x = ref a in
    while Array.length !x > 0 do
      let q, r = divmod_small !x chunk in
      parts := r :: !parts; x := q
    done;
    match !parts with
    | [] -> "0"
    | hd :: tl -> String.concat "" (string_of_int hd :: List.map (Printf.sprintf "%07d") tl)
  end
