(* Allocation-free scanner for the frequent NDJSON line shapes (names, levels,
   expressions).  A line is flattened into slots: a key whose value is an object
   becomes the line's [kind]; scalar values are stored in per-key slots.  Any
   unexpected shape returns [false] and the caller falls back to the generic
   JSON parser, so this is purely an optimisation. *)

(* key ids *)
let keys = [| "in"; "il"; "ie"; "str"; "num"; "pre"; "i"; "succ"; "max"; "imax"; "param";
              "bvar"; "sort"; "const"; "name"; "us"; "app"; "fn"; "arg"; "lam"; "forallE";
              "type"; "body"; "binderInfo"; "letE"; "value"; "nondep"; "proj"; "typeName";
              "idx"; "struct"; "natVal"; "strVal" |]
let nkeys = Array.length keys
let k_in = 0 and k_il = 1 and k_ie = 2 and k_str = 3 and k_num = 4 and k_pre = 5 and k_i = 6
and k_succ = 7 and k_max = 8 and k_imax = 9 and k_param = 10 and k_bvar = 11 and k_sort = 12
and k_const = 13 and k_name = 14 and k_us = 15 and k_app = 16 and k_fn = 17 and k_arg = 18
and k_lam = 19 and k_forall = 20 and k_type = 21 and k_body = 22 and k_bi = 23 and k_let = 24
and k_value = 25 and k_nondep = 26 and k_proj = 27 and k_typename = 28 and k_idx = 29
and k_struct = 30 and k_natval = 31 and k_strval = 32

exception Fallback

type st = {
  ints : int array;            (* int value per key, or min_int *)
  sstart : int array;          (* string value: start/len per key (len -1 = none) *)
  slen : int array;
  mutable kind : int;          (* key of the (first) object-valued field *)
  arr : int array;             (* int array value (only for "us"/"max"/"imax") *)
  mutable arr_n : int;
  mutable arr_key : int;
}

let create () = { ints = Array.make nkeys min_int; sstart = Array.make nkeys 0; slen = Array.make nkeys (-1);
                  kind = -1; arr = Array.make 64 0; arr_n = 0; arr_key = -1 }

let reset st =
  for i = 0 to nkeys - 1 do
    Array.unsafe_set st.ints i min_int;
    Array.unsafe_set st.slen i (-1)
  done;
  st.kind <- -1; st.arr_n <- 0; st.arr_key <- -1

let[@inline] eq_key (s : bytes) start (key : string) len =
  let rec eq j =
    j >= len || (Bytes.unsafe_get s (start + j) = String.unsafe_get key j && eq (j + 1)) in
  eq 0

let key_id (s : bytes) start len =
  match len with
  | 1 -> if Bytes.unsafe_get s start = 'i' then k_i else raise Fallback
  | 2 ->
    (match Bytes.unsafe_get s start with
     | 'i' ->
       (match Bytes.unsafe_get s (start + 1) with
        | 'e' -> k_ie | 'n' -> k_in | 'l' -> k_il | _ -> raise Fallback)
     | 'f' -> if Bytes.unsafe_get s (start + 1) = 'n' then k_fn else raise Fallback
     | 'u' -> if Bytes.unsafe_get s (start + 1) = 's' then k_us else raise Fallback
     | _ -> raise Fallback)
  | 3 ->
    (match Bytes.unsafe_get s start with
     | 'a' ->
       if eq_key s start "app" 3 then k_app
       else if eq_key s start "arg" 3 then k_arg
       else raise Fallback
     | 's' -> if eq_key s start "str" 3 then k_str else raise Fallback
     | 'n' -> if eq_key s start "num" 3 then k_num else raise Fallback
     | 'p' -> if eq_key s start "pre" 3 then k_pre else raise Fallback
     | 'l' -> if eq_key s start "lam" 3 then k_lam else raise Fallback
     | 'm' -> if eq_key s start "max" 3 then k_max else raise Fallback
     | 'i' -> if eq_key s start "idx" 3 then k_idx else raise Fallback
     | _ -> raise Fallback)
  | 4 ->
    (match Bytes.unsafe_get s start with
     | 't' -> if eq_key s start "type" 4 then k_type else raise Fallback
     | 'b' ->
       if eq_key s start "body" 4 then k_body
       else if eq_key s start "bvar" 4 then k_bvar
       else raise Fallback
     | 'n' -> if eq_key s start "name" 4 then k_name else raise Fallback
     | 's' ->
       if eq_key s start "sort" 4 then k_sort
       else if eq_key s start "succ" 4 then k_succ
       else raise Fallback
     | 'i' -> if eq_key s start "imax" 4 then k_imax else raise Fallback
     | 'l' -> if eq_key s start "letE" 4 then k_let else raise Fallback
     | 'p' -> if eq_key s start "proj" 4 then k_proj else raise Fallback
     | _ -> raise Fallback)
  | 5 ->
    (match Bytes.unsafe_get s start with
     | 'c' -> if eq_key s start "const" 5 then k_const else raise Fallback
     | 'v' -> if eq_key s start "value" 5 then k_value else raise Fallback
     | 'p' -> if eq_key s start "param" 5 then k_param else raise Fallback
     | _ -> raise Fallback)
  | 6 ->
    (match Bytes.unsafe_get s start with
     | 'n' ->
       if eq_key s start "nondep" 6 then k_nondep
       else if eq_key s start "natVal" 6 then k_natval
       else raise Fallback
     | 's' ->
       if eq_key s start "struct" 6 then k_struct
       else if eq_key s start "strVal" 6 then k_strval
       else raise Fallback
     | _ -> raise Fallback)
  | 7 -> if eq_key s start "forallE" 7 then k_forall else raise Fallback
  | 8 -> if eq_key s start "typeName" 8 then k_typename else raise Fallback
  | 10 -> if eq_key s start "binderInfo" 10 then k_bi else raise Fallback
  | _ -> raise Fallback

let scan_bytes st (s : bytes) off len : bool =
  reset st;
  let stop = off + len in
  let p = ref off in
  let peek () = if !p < stop then Bytes.unsafe_get s !p else '\000' in
  let ws () = while !p < stop && (let c = Bytes.unsafe_get s !p in c = ' ' || c = '\t' || c = '\r') do incr p done in
  let expect c = ws (); if peek () = c then incr p else raise Fallback in
  (* string without escapes: returns (start, len) *)
  let str () =
    expect '"';
    let start = !p in
    while !p < stop && (let c = Bytes.unsafe_get s !p in c <> '"' && c <> '\\') do incr p done;
    if peek () <> '"' then raise Fallback;
    let l = !p - start in incr p; (start, l) in
  let int () =
    ws ();
    let neg = peek () = '-' in if neg then incr p;
    let start = !p in
    let v = ref 0 in
    while !p < stop && (let c = Bytes.unsafe_get s !p in c >= '0' && c <= '9') do
      if !v > (max_int - 9) / 10 then raise Fallback;
      v := !v * 10 + (Char.code (Bytes.unsafe_get s !p) - 48); incr p
    done;
    if !p = start then raise Fallback;
    if neg then raise Fallback;
    !v in
  let rec obj () =
    expect '{';
    ws ();
    if peek () = '}' then incr p
    else begin
      let continue = ref true in
      while !continue do
        let (ks, kl) = str () in
        let k = key_id s ks kl in
        expect ':'; ws ();
        (match peek () with
         | '{' -> if st.kind < 0 then st.kind <- k; obj ()
         | '"' -> let (a, l) = str () in st.sstart.(k) <- a; st.slen.(k) <- l
         | '[' ->
           incr p; ws ();
           if st.arr_key >= 0 then raise Fallback;
           st.arr_key <- k;
           if peek () = ']' then incr p
           else begin
             let more = ref true in
             while !more do
               let v = int () in
               if st.arr_n >= Array.length st.arr then raise Fallback;
               st.arr.(st.arr_n) <- v; st.arr_n <- st.arr_n + 1;
               ws ();
               (match peek () with ',' -> incr p | ']' -> incr p; more := false | _ -> raise Fallback)
             done
           end
         | 't' -> if !p + 4 <= stop && eq_key s !p "true" 4 then (p := !p + 4; st.ints.(k) <- 1) else raise Fallback
         | 'f' -> if !p + 5 <= stop && eq_key s !p "false" 5 then (p := !p + 5; st.ints.(k) <- 0) else raise Fallback
         | _ -> st.ints.(k) <- int ());
        ws ();
        (match peek () with ',' -> incr p | '}' -> incr p; continue := false | _ -> raise Fallback)
      done
    end in
  try obj (); ws (); !p = stop with Fallback -> false

let scan st (s : string) : bool =
  scan_bytes st (Bytes.unsafe_of_string s) 0 (String.length s)

