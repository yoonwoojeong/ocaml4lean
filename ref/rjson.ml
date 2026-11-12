(* A small JSON reader for the NDJSON export lines (reference checker). *)

type t =
  | Null
  | Bool of bool
  | Int of int
  | Num of string          (* an integer too large for [int], kept as its digits *)
  | Str of string
  | List of t list
  | Obj of (string * t) list

exception Error of string
let err fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt

let add_utf8 b cp =
  if cp < 0x80 then Buffer.add_char b (Char.chr cp)
  else if cp < 0x800 then begin
    Buffer.add_char b (Char.chr (0xC0 lor (cp lsr 6)));
    Buffer.add_char b (Char.chr (0x80 lor (cp land 0x3F)))
  end else if cp < 0x10000 then begin
    Buffer.add_char b (Char.chr (0xE0 lor (cp lsr 12)));
    Buffer.add_char b (Char.chr (0x80 lor ((cp lsr 6) land 0x3F)));
    Buffer.add_char b (Char.chr (0x80 lor (cp land 0x3F)))
  end else begin
    Buffer.add_char b (Char.chr (0xF0 lor (cp lsr 18)));
    Buffer.add_char b (Char.chr (0x80 lor ((cp lsr 12) land 0x3F)));
    Buffer.add_char b (Char.chr (0x80 lor ((cp lsr 6) land 0x3F)));
    Buffer.add_char b (Char.chr (0x80 lor (cp land 0x3F)))
  end

let parse (s : string) : t =
  let n = String.length s in
  let pos = ref 0 in
  let peek () = if !pos < n then s.[!pos] else '\000' in
  let skip_ws () = while !pos < n && (match s.[!pos] with ' ' | '\t' | '\r' | '\n' -> true | _ -> false) do incr pos done in
  let expect c = if peek () = c && !pos < n then incr pos else err "expected '%c' at %d" c !pos in
  let hex4 () =
    if !pos + 4 > n then err "bad \\u escape";
    let v = ref 0 in
    for k = 0 to 3 do
      let c = s.[!pos + k] in
      let d = match c with
        | '0' .. '9' -> Char.code c - 48
        | 'a' .. 'f' -> Char.code c - 87
        | 'A' .. 'F' -> Char.code c - 55
        | _ -> err "bad hex digit" in
      v := !v * 16 + d
    done;
    pos := !pos + 4; !v in
  let string_ () =
    expect '"';
    let b = Buffer.create 16 in
    let fin = ref false in
    while not !fin do
      if !pos >= n then err "unterminated string";
      let c = s.[!pos] in
      incr pos;
      if c = '"' then fin := true
      else if c = '\\' then begin
        if !pos >= n then err "bad escape";
        let e = s.[!pos] in
        incr pos;
        match e with
        | '"' -> Buffer.add_char b '"' | '\\' -> Buffer.add_char b '\\' | '/' -> Buffer.add_char b '/'
        | 'b' -> Buffer.add_char b '\b' | 'f' -> Buffer.add_char b '\012' | 'n' -> Buffer.add_char b '\n'
        | 'r' -> Buffer.add_char b '\r' | 't' -> Buffer.add_char b '\t'
        | 'u' ->
          let hi = hex4 () in
          if hi >= 0xD800 && hi < 0xDC00 && !pos + 1 < n && s.[!pos] = '\\' && s.[!pos + 1] = 'u' then begin
            pos := !pos + 2;
            let lo = hex4 () in
            if lo >= 0xDC00 && lo < 0xE000 then add_utf8 b (0x10000 + ((hi - 0xD800) lsl 10) + (lo - 0xDC00))
            else (add_utf8 b hi; add_utf8 b lo)
          end else add_utf8 b hi
        | _ -> err "bad escape"
      end else Buffer.add_char b c
    done;
    Buffer.contents b in
  let rec value () =
    skip_ws ();
    match peek () with
    | '{' ->
      incr pos; skip_ws ();
      if peek () = '}' then (incr pos; Obj [])
      else begin
        let fields = ref [] in
        let fin = ref false in
        while not !fin do
          skip_ws ();
          let k = string_ () in
          skip_ws (); expect ':';
          let v = value () in
          fields := (k, v) :: !fields;
          skip_ws ();
          if peek () = ',' then incr pos else (expect '}'; fin := true)
        done;
        Obj (List.rev !fields)
      end
    | '[' ->
      incr pos; skip_ws ();
      if peek () = ']' then (incr pos; List [])
      else begin
        let items = ref [] in
        let fin = ref false in
        while not !fin do
          items := value () :: !items;
          skip_ws ();
          if peek () = ',' then incr pos else (expect ']'; fin := true)
        done;
        List (List.rev !items)
      end
    | '"' -> Str (string_ ())
    | 't' when !pos + 4 <= n && String.sub s !pos 4 = "true" -> pos := !pos + 4; Bool true
    | 'f' when !pos + 5 <= n && String.sub s !pos 5 = "false" -> pos := !pos + 5; Bool false
    | 'n' when !pos + 4 <= n && String.sub s !pos 4 = "null" -> pos := !pos + 4; Null
    | '-' | '0' .. '9' ->
      let st = !pos in
      incr pos;
      while !pos < n && (match s.[!pos] with '0' .. '9' -> true | _ -> false) do incr pos done;
      let lit = String.sub s st (!pos - st) in
      (match int_of_string_opt lit with Some i -> Int i | None -> Num lit)
    | c -> err "unexpected '%c' at %d" c !pos in
  let v = value () in
  skip_ws ();
  if !pos <> n then err "trailing characters";
  v

let field k = function
  | Obj fs -> (match List.assoc_opt k fs with Some v -> v | None -> err "missing field %s" k)
  | _ -> err "not an object (looking for %s)" k
let field_opt k = function Obj fs -> List.assoc_opt k fs | _ -> None
let to_int = function Int i -> i | _ -> err "expected integer"
let to_str = function Str s -> s | _ -> err "expected string"
let to_bool = function Bool b -> b | _ -> err "expected bool"
let to_list = function List l -> l | _ -> err "expected list"
