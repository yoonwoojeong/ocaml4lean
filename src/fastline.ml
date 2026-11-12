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
  sstart : int array;          (* string value: start/len per key (len -1 = none);
                                  start is an offset in the scanned buffer *)
  slen : int array;
  mutable kind : int;          (* key of the (first) object-valued field *)
  arr : int array;             (* int array value (only for "us"/"max"/"imax") *)
  mutable arr_n : int;
  mutable arr_key : int;
  touched : int array;         (* keys set by the last scan, to reset only those *)
  mutable ntouched : int;
}

let create () = { ints = Array.make nkeys min_int; sstart = Array.make nkeys 0; slen = Array.make nkeys (-1);
                  kind = -1; arr = Array.make 64 0; arr_n = 0; arr_key = -1;
                  touched = Array.make 64 0; ntouched = 0 }

let reset st =
  for j = 0 to st.ntouched - 1 do
    let k = Array.unsafe_get st.touched j in
    Array.unsafe_set st.ints k min_int; Array.unsafe_set st.slen k (-1)
  done;
  st.ntouched <- 0; st.kind <- -1; st.arr_n <- 0; st.arr_key <- -1

let touch st k =
  if st.ntouched >= Array.length st.touched then raise Fallback;
  Array.unsafe_set st.touched st.ntouched k; st.ntouched <- st.ntouched + 1

(* key lookup: a direct-mapped table indexed by (length, first and last
   character); the candidate is then compared in full.  Keys that collide in
   the table are found by linear search (none do for the current key set). *)
let slot len c0 cl = (len * 37 + Char.code c0 * 11 + Char.code cl) land 1023
let key_tbl =
  let t = Array.make 1024 (-1) in
  Array.iteri (fun k key ->
      let i = slot (String.length key) key.[0] key.[String.length key - 1] in
      t.(i) <- (if t.(i) = -1 then k else -2)) keys;
  t

let key_eq s start len k =
  let key = Array.unsafe_get keys k in
  String.length key = len &&
  (let rec eq j = j >= len || (Bytes.unsafe_get s (start + j) = String.unsafe_get key j && eq (j + 1)) in eq 0)

let key_id (s : Bytes.t) start len =
  if len = 0 then raise Fallback;
  match Array.unsafe_get key_tbl (slot len (Bytes.unsafe_get s start) (Bytes.unsafe_get s (start + len - 1))) with
  | -1 -> raise Fallback
  | -2 ->
    let rec go k = if k >= nkeys then raise Fallback else if key_eq s start len k then k else go (k + 1) in
    go 0
  | k -> if key_eq s start len k then k else raise Fallback

(* scan one object starting at [start], reading no further than [stop]:
   returns the position after it and any trailing blanks, or -1 *)
let scan_prefix st (s : Bytes.t) start stop : int =
  reset st;
  let n = stop in
  let p = ref start in
  let peek () = if !p < n then Bytes.unsafe_get s !p else '\000' in
  let ws () = while !p < n && (let c = Bytes.unsafe_get s !p in c = ' ' || c = '\t' || c = '\r') do incr p done in
  let expect c = ws (); if peek () = c then incr p else raise Fallback in
  (* string without escapes: returns (start, len) *)
  let str () =
    expect '"';
    let start = !p in
    while !p < n && (let c = Bytes.unsafe_get s !p in c <> '"' && c <> '\\') do incr p done;
    if peek () <> '"' then raise Fallback;
    let len = !p - start in incr p; (start, len) in
  let int () =
    ws ();
    let neg = peek () = '-' in if neg then incr p;
    let start = !p in
    let v = ref 0 in
    while !p < n && (let c = Bytes.unsafe_get s !p in c >= '0' && c <= '9') do
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
         | '"' -> let (a, l) = str () in touch st k; st.sstart.(k) <- a; st.slen.(k) <- l
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
         | 't' -> if !p + 4 <= n && Bytes.sub_string s !p 4 = "true" then (p := !p + 4; touch st k; st.ints.(k) <- 1) else raise Fallback
         | 'f' -> if !p + 5 <= n && Bytes.sub_string s !p 5 = "false" then (p := !p + 5; touch st k; st.ints.(k) <- 0) else raise Fallback
         | _ -> let v = int () in touch st k; st.ints.(k) <- v);
        ws ();
        (match peek () with ',' -> incr p | '}' -> incr p; continue := false | _ -> raise Fallback)
      done
    end in
  try obj (); ws (); !p with Fallback -> -1

(* scan the line s[start, stop) *)
let scan st s start stop = scan_prefix st s start stop = stop
