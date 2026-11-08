(* Minimal JSON parser, sufficient for lean4export NDJSON lines. *)
type t =
  | Null
  | Bool of bool
  | Int of int
  | Num of string          (* numbers that do not fit an int / are not integers *)
  | Str of string
  | Arr of t list
  | Obj of (string * t) list

exception Error of string

let parse (s : string) : t =
  let n = String.length s in
  let p = ref 0 in
  let err m = raise (Error (Printf.sprintf "%s at %d" m !p)) in
  let rec ws () = if !p < n && (match s.[!p] with ' ' | '\t' | '\n' | '\r' -> true | _ -> false) then (incr p; ws ()) in
  let expect c = if !p < n && s.[!p] = c then incr p else err (Printf.sprintf "expected '%c'" c) in
  let add_utf8 b c =
    if c < 0x80 then Buffer.add_char b (Char.chr c)
    else if c < 0x800 then (Buffer.add_char b (Char.chr (0xC0 lor (c lsr 6)));
                            Buffer.add_char b (Char.chr (0x80 lor (c land 0x3F))))
    else if c < 0x10000 then (Buffer.add_char b (Char.chr (0xE0 lor (c lsr 12)));
                              Buffer.add_char b (Char.chr (0x80 lor ((c lsr 6) land 0x3F)));
                              Buffer.add_char b (Char.chr (0x80 lor (c land 0x3F))))
    else (Buffer.add_char b (Char.chr (0xF0 lor (c lsr 18)));
          Buffer.add_char b (Char.chr (0x80 lor ((c lsr 12) land 0x3F)));
          Buffer.add_char b (Char.chr (0x80 lor ((c lsr 6) land 0x3F)));
          Buffer.add_char b (Char.chr (0x80 lor (c land 0x3F)))) in
  let hex4 () =
    if !p + 4 > n then err "bad \\u";
    let v = int_of_string ("0x" ^ String.sub s !p 4) in p := !p + 4; v in
  let str () =
    expect '"';
    let start = !p in
    (* fast path: no escapes *)
    while !p < n && s.[!p] <> '"' && s.[!p] <> '\\' do incr p done;
    if !p < n && s.[!p] = '"' then (let r = String.sub s start (!p - start) in incr p; r)
    else begin
      let b = Buffer.create 32 in
      Buffer.add_substring b s start (!p - start);
      let fin = ref false in
      while not !fin do
        if !p >= n then err "unterminated string";
        let c = s.[!p] in
        incr p;
        if c = '"' then fin := true
        else if c = '\\' then begin
          if !p >= n then err "bad escape";
          let e = s.[!p] in incr p;
          match e with
          | '"' -> Buffer.add_char b '"' | '\\' -> Buffer.add_char b '\\'
          | '/' -> Buffer.add_char b '/' | 'b' -> Buffer.add_char b '\b'
          | 'f' -> Buffer.add_char b '\012' | 'n' -> Buffer.add_char b '\n'
          | 'r' -> Buffer.add_char b '\r' | 't' -> Buffer.add_char b '\t'
          | 'u' ->
            let c1 = hex4 () in
            if c1 >= 0xD800 && c1 < 0xDC00 && !p + 6 <= n && s.[!p] = '\\' && s.[!p+1] = 'u' then begin
              p := !p + 2;
              let c2 = hex4 () in
              if c2 >= 0xDC00 && c2 < 0xE000 then
                add_utf8 b (0x10000 + ((c1 - 0xD800) lsl 10) + (c2 - 0xDC00))
              else (add_utf8 b c1; add_utf8 b c2)
            end else add_utf8 b c1
          | _ -> err "bad escape"
        end else Buffer.add_char b c
      done;
      Buffer.contents b
    end in
  let rec value () =
    ws ();
    if !p >= n then err "eof";
    match s.[!p] with
    | '{' ->
      incr p; ws ();
      if !p < n && s.[!p] = '}' then (incr p; Obj [])
      else begin
        let rec fields acc =
          ws (); let k = str () in ws (); expect ':';
          let v = value () in ws ();
          if !p < n && s.[!p] = ',' then (incr p; fields ((k, v) :: acc))
          else (expect '}'; Obj (List.rev ((k, v) :: acc))) in
        fields []
      end
    | '[' ->
      incr p; ws ();
      if !p < n && s.[!p] = ']' then (incr p; Arr [])
      else begin
        let rec elems acc =
          let v = value () in ws ();
          if !p < n && s.[!p] = ',' then (incr p; elems (v :: acc))
          else (expect ']'; Arr (List.rev (v :: acc))) in
        elems []
      end
    | '"' -> Str (str ())
    | 't' -> if !p + 4 <= n && String.sub s !p 4 = "true" then (p := !p + 4; Bool true) else err "bad literal"
    | 'f' -> if !p + 5 <= n && String.sub s !p 5 = "false" then (p := !p + 5; Bool false) else err "bad literal"
    | 'n' -> if !p + 4 <= n && String.sub s !p 4 = "null" then (p := !p + 4; Null) else err "bad literal"
    | _ ->
      let start = !p in
      while !p < n && (match s.[!p] with '0'..'9' | '-' | '+' | '.' | 'e' | 'E' -> true | _ -> false) do incr p done;
      if !p = start then err "unexpected character";
      let t = String.sub s start (!p - start) in
      (match int_of_string_opt t with Some i when String.length t < 18 -> Int i | _ -> Num t) in
  let v = value () in
  ws ();
  if !p <> n then err "trailing data";
  v

let field k = function
  | Obj l -> (try List.assoc k l with Not_found -> raise (Error ("missing field " ^ k)))
  | _ -> raise (Error ("not an object, wanted " ^ k))
let field_opt k = function Obj l -> List.assoc_opt k l | _ -> None
let to_int = function Int i -> i | _ -> raise (Error "expected int")
let to_bool = function Bool b -> b | _ -> raise (Error "expected bool")
let to_str = function Str s -> s | _ -> raise (Error "expected string")
let to_list = function Arr l -> l | _ -> raise (Error "expected array")
