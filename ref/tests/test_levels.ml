(* Cross-check of the reference checker's exact universe-level decision procedure
   (rterm.ml) against brute-force evaluation on random levels over 3 parameters.
   Run: ref/tests/run_levels.sh *)
open Rterm
let ps = [| [S "a"]; [S "b"]; [S "c"] |]
let rec gen d =
  if d = 0 then (match Random.int 5 with 0 -> Zero | 1 -> Succ Zero | n -> Param ps.(n - 2))
  else match Random.int 6 with
    | 0 -> Succ (gen (d - 1))
    | 1 | 2 -> Max (gen (d - 1), gen (d - 1))
    | 3 | 4 -> IMax (gen (d - 1), gen (d - 1))
    | _ -> gen 0
let rec ev s = function
  | Zero -> 0 | Succ l -> 1 + ev s l
  | Max (a, b) -> max (ev s a) (ev s b)
  | IMax (a, b) -> let vb = ev s b in if vb = 0 then 0 else max (ev s a) vb
  | Param n -> List.assoc n s
let brute f =
  let r = ref true in
  for a = 0 to 7 do for b = 0 to 7 do for c = 0 to 7 do
    if not (f [ (ps.(0), a); (ps.(1), b); (ps.(2), c) ]) then r := false done done done; !r
let () =
  Random.init 42;
  let bad = ref 0 and n = 20000 and nt = ref 0 and nf = ref 0 in
  for _ = 1 to n do
    let a = gen (1 + Random.int 4) and b = gen (1 + Random.int 4) in
    let g = brute (fun s -> ev s a >= ev s b) and e = brute (fun s -> ev s a = ev s b) in
    let g' = level_geq a b and e' = level_equiv a b in
    if g then incr nt else incr nf;
    if g <> g' || e <> e' then begin
      incr bad;
      if !bad < 6 then Printf.printf "MISMATCH geq brute=%b algo=%b equiv brute=%b algo=%b\n  a=%s\n  b=%s\n" g g' e e' (level_to_string a) (level_to_string b)
    end;
    if brute (fun s -> ev s a = 0) <> level_is_zero a then (incr bad; Printf.printf "is_zero mismatch %s\n" (level_to_string a));
    if brute (fun s -> ev s a >= 1) <> level_never_zero a then (incr bad; Printf.printf "never_zero mismatch %s\n" (level_to_string a))
  done;
  Printf.printf "%d random pairs (%d geq true, %d false), %d mismatches\n" n !nt !nf !bad
