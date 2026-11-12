(* Natural numbers of arbitrary size, for Nat literals in the reference checker.
   Deliberately simple: little-endian limbs in base 2^24, always normalised
   (no most-significant zero limb), schoolbook algorithms.  Speed is irrelevant. *)

type t = int array

let bits = 24
let base = 1 lsl bits
let mask = base - 1

let norm (a : int array) : t =
  let n = ref (Array.length a) in
  while !n > 0 && a.(!n - 1) = 0 do decr n done;
  if !n = Array.length a then a else Array.sub a 0 !n

let zero : t = [||]
let is_zero (a : t) = Array.length a = 0

let of_int (n : int) : t =
  if n < 0 then invalid_arg "Rbig.of_int";
  let rec go n acc = if n = 0 then List.rev acc else go (n lsr bits) ((n land mask) :: acc) in
  Array.of_list (go n [])

let one = of_int 1

let to_int_opt (a : t) : int option =
  if Array.length a > 2 then None
  else Some (Array.fold_right (fun l acc -> (acc lsl bits) lor l) a 0)

let compare (a : t) (b : t) : int =
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

let add (a : t) (b : t) : t =
  let n = max (Array.length a) (Array.length b) + 1 in
  let r = Array.make n 0 in
  let carry = ref 0 in
  for i = 0 to n - 1 do
    let x = (if i < Array.length a then a.(i) else 0) + (if i < Array.length b then b.(i) else 0) + !carry in
    r.(i) <- x land mask; carry := x lsr bits
  done;
  norm r

(* a - b, requires a >= b *)
let sub (a : t) (b : t) : t =
  if compare a b < 0 then invalid_arg "Rbig.sub";
  let r = Array.make (Array.length a) 0 in
  let borrow = ref 0 in
  for i = 0 to Array.length a - 1 do
    let x = a.(i) - (if i < Array.length b then b.(i) else 0) - !borrow in
    if x < 0 then (r.(i) <- x + base; borrow := 1) else (r.(i) <- x; borrow := 0)
  done;
  norm r

let mul (a : t) (b : t) : t =
  if is_zero a || is_zero b then zero else begin
    let r = Array.make (Array.length a + Array.length b + 1) 0 in
    for i = 0 to Array.length a - 1 do
      let carry = ref 0 in
      for j = 0 to Array.length b - 1 do
        let x = r.(i + j) + a.(i) * b.(j) + !carry in
        r.(i + j) <- x land mask; carry := x lsr bits
      done;
      let k = ref (i + Array.length b) in
      while !carry <> 0 do
        let x = r.(!k) + !carry in
        r.(!k) <- x land mask; carry := x lsr bits; incr k
      done
    done;
    norm r
  end

let numbits (a : t) : int =
  let n = Array.length a in
  if n = 0 then 0 else begin
    let top = ref a.(n - 1) and k = ref 0 in
    while !top <> 0 do incr k; top := !top lsr 1 done;
    (n - 1) * bits + !k
  end

let testbit (a : t) (i : int) : bool =
  let l = i / bits in
  l < Array.length a && (a.(l) lsr (i mod bits)) land 1 = 1

let shift_left (a : t) (k : int) : t =
  if is_zero a then zero else begin
    let limbs = k / bits and sh = k mod bits in
    let r = Array.make (Array.length a + limbs + 1) 0 in
    for i = 0 to Array.length a - 1 do
      let x = a.(i) lsl sh in
      r.(i + limbs) <- r.(i + limbs) lor (x land mask);
      r.(i + limbs + 1) <- r.(i + limbs + 1) lor (x lsr bits)
    done;
    norm r
  end

let shift_right (a : t) (k : int) : t =
  let limbs = k / bits and sh = k mod bits in
  if limbs >= Array.length a then zero else begin
    let n = Array.length a - limbs in
    let r = Array.make n 0 in
    for i = 0 to n - 1 do
      let lo = a.(i + limbs) lsr sh in
      let hi = if i + limbs + 1 < Array.length a then (a.(i + limbs + 1) lsl (bits - sh)) land mask else 0 in
      r.(i) <- lo lor hi
    done;
    norm r
  end

(* quotient and remainder by long division, one bit at a time *)
let divmod (a : t) (b : t) : t * t =
  if is_zero b then invalid_arg "Rbig.divmod";
  let q = Array.make (Array.length a) 0 in
  let r = ref zero in
  for i = numbits a - 1 downto 0 do
    r := shift_left !r 1;
    if testbit a i then r := add !r one;
    if compare !r b >= 0 then begin
      r := sub !r b;
      q.(i / bits) <- q.(i / bits) lor (1 lsl (i mod bits))
    end
  done;
  (norm q, !r)

let rec gcd a b = if is_zero b then a else gcd b (snd (divmod a b))

let pow (a : t) (k : int) : t =
  let rec go acc base k =
    if k = 0 then acc
    else go (if k land 1 = 1 then mul acc base else acc) (mul base base) (k lsr 1) in
  go one a k

let bitwise f (a : t) (b : t) : t =
  let n = max (Array.length a) (Array.length b) in
  norm (Array.init n (fun i ->
      f (if i < Array.length a then a.(i) else 0) (if i < Array.length b then b.(i) else 0)))

let logand = bitwise ( land )
let logor = bitwise ( lor )
let logxor = bitwise ( lxor )

let succ a = add a one
let pred a = sub a one

let of_string (s : string) : t =
  if s = "" then invalid_arg "Rbig.of_string";
  let r = ref zero in
  String.iter (fun c ->
      if c < '0' || c > '9' then invalid_arg "Rbig.of_string";
      r := add (mul !r (of_int 10)) (of_int (Char.code c - 48))) s;
  !r

let to_string (a : t) : string =
  if is_zero a then "0" else begin
    let digits = Buffer.create 16 in
    let r = ref a in
    let ten = of_int 10 in
    let acc = ref [] in
    while not (is_zero !r) do
      let q, m = divmod !r ten in
      acc := (match to_int_opt m with Some d -> d | None -> 0) :: !acc;
      r := q
    done;
    List.iter (fun d -> Buffer.add_char digits (Char.chr (48 + d))) !acc;
    Buffer.contents digits
  end
