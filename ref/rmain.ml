(* Driver of the reference checker: reads a lean4export NDJSON file and checks
   its declarations one block at a time, in file order, stopping at the first
   failure.  Exit codes (as the arena expects): 0 accepted, 1 rejected,
   3 could not decide (malformed input, resource exhaustion, internal error). *)
open Rterm
open Rtc
module J = Rjson

exception Bad of string
let bad fmt = Printf.ksprintf (fun s -> raise (Bad s)) fmt

type tables = {
  names : (int, name) Hashtbl.t;
  levels : (int, level) Hashtbl.t;
  exprs : (int, term) Hashtbl.t;
}

let get tbl i what = match Hashtbl.find_opt tbl i with Some x -> x | None -> bad "undefined %s reference %d" what i

let parse_file (path : string) : Rdecl.block list =
  let ic = if path = "-" then stdin else open_in_bin path in
  let tb = { names = Hashtbl.create 1000; levels = Hashtbl.create 1000; exprs = Hashtbl.create 100000 } in
  Hashtbl.replace tb.names 0 [];
  Hashtbl.replace tb.levels 0 Zero;
  let name j = get tb.names (J.to_int j) "name" in
  let level j = get tb.levels (J.to_int j) "level" in
  let expr j = get tb.exprs (J.to_int j) "expr" in
  let names j = List.map name (J.to_list j) in
  let def tbl i v what = if Hashtbl.mem tbl i then bad "duplicate %s index %d" what i; Hashtbl.replace tbl i v in
  let blocks = ref [] in
  let pending_quot = ref [] in
  let flush () = if !pending_quot <> [] then (blocks := Rdecl.QuotBlock (List.rev !pending_quot) :: !blocks; pending_quot := []) in
  let push b = flush (); blocks := b :: !blocks in
  let mk name lparams ty kind unsafe = { name; lparams; ty; kind; unsafe } in
  let line s =
    match J.parse s with
    | J.Obj fields ->
      let has k = List.mem_assoc k fields and f k = List.assoc k fields in
      if has "in" then begin
        let i = J.to_int (f "in") in
        let n =
          if has "str" then (let o = f "str" in name (J.field "pre" o) @ [S (J.to_str (J.field "str" o))])
          else if has "num" then (let o = f "num" in name (J.field "pre" o) @ [N (J.to_int (J.field "i" o))])
          else bad "bad name line" in
        def tb.names i n "name"
      end else if has "il" then begin
        let i = J.to_int (f "il") in
        let l =
          if has "succ" then Succ (level (f "succ"))
          else if has "max" then (match J.to_list (f "max") with [a; b] -> Max (level a, level b) | _ -> bad "bad max")
          else if has "imax" then (match J.to_list (f "imax") with [a; b] -> IMax (level a, level b) | _ -> bad "bad imax")
          else if has "param" then Param (name (f "param"))
          else bad "bad level line" in
        def tb.levels i l "level"
      end else if has "ie" then begin
        let i = J.to_int (f "ie") in
        let e =
          if has "bvar" then Bvar (J.to_int (f "bvar"))
          else if has "sort" then Sort (level (f "sort"))
          else if has "const" then
            (let o = f "const" in Const (name (J.field "name" o), List.map level (J.to_list (J.field "us" o))))
          else if has "app" then (let o = f "app" in App (expr (J.field "fn" o), expr (J.field "arg" o)))
          else if has "lam" then (let o = f "lam" in Lam (expr (J.field "type" o), expr (J.field "body" o)))
          else if has "forallE" then (let o = f "forallE" in Pi (expr (J.field "type" o), expr (J.field "body" o)))
          else if has "letE" then
            (let o = f "letE" in Let (expr (J.field "type" o), expr (J.field "value" o), expr (J.field "body" o)))
          else if has "proj" then begin
            let o = f "proj" in
            let idx = J.to_int (J.field "idx" o) in
            if idx < 0 then bad "negative projection index";
            Proj (name (J.field "typeName" o), idx, expr (J.field "struct" o))
          end
          else if has "natVal" then
            (match f "natVal" with
             | J.Str s | J.Num s -> Nat (Rbig.of_string s)
             | J.Int n when n >= 0 -> Nat (Rbig.of_int n)
             | _ -> bad "bad natVal")
          else if has "strVal" then Str (J.to_str (f "strVal"))
          else if has "mdata" then expr (J.field "expr" (f "mdata"))
          else bad "bad expr line" in
        def tb.exprs i e "expr"
      end else if has "axiom" then begin
        let o = f "axiom" in
        push (Rdecl.Single (mk (name (J.field "name" o)) (names (J.field "levelParams" o)) (expr (J.field "type" o))
                              Axiom (J.to_bool (J.field "isUnsafe" o))))
      end else if has "def" then begin
        let o = f "def" in
        let hints = match J.field "hints" o with
          | J.Str "opaque" -> HOpaque | J.Str "abbrev" -> HAbbrev
          | J.Obj [ ("regular", J.Int h) ] -> HRegular h
          | _ -> bad "bad hints" in
        let safety = match J.field "safety" o with
          | J.Str "safe" -> Safe | J.Str "unsafe" -> Unsafe | J.Str "partial" -> Partial
          | _ -> bad "bad safety" in
        push (Rdecl.Single (mk (name (J.field "name" o)) (names (J.field "levelParams" o)) (expr (J.field "type" o))
                              (Defn { value = expr (J.field "value" o); hints; safety; all = names (J.field "all" o) })
                              (safety = Unsafe)))
      end else if has "thm" then begin
        let o = f "thm" in
        push (Rdecl.Single (mk (name (J.field "name" o)) (names (J.field "levelParams" o)) (expr (J.field "type" o))
                              (Thm { value = expr (J.field "value" o) }) false))
      end else if has "opaque" then begin
        let o = f "opaque" in
        push (Rdecl.Single (mk (name (J.field "name" o)) (names (J.field "levelParams" o)) (expr (J.field "type" o))
                              (Opaq { value = expr (J.field "value" o) }) (J.to_bool (J.field "isUnsafe" o))))
      end else if has "quot" then begin
        let o = f "quot" in
        let k = match J.field "kind" o with
          | J.Str "type" -> QType | J.Str "ctor" -> QCtor | J.Str "lift" -> QLift | J.Str "ind" -> QInd
          | _ -> bad "bad quot kind" in
        pending_quot := mk (name (J.field "name" o)) (names (J.field "levelParams" o)) (expr (J.field "type" o)) (Quot k) false
                        :: !pending_quot
      end else if has "inductive" then begin
        let o = f "inductive" in
        let ty o = mk (name (J.field "name" o)) (names (J.field "levelParams" o)) (expr (J.field "type" o))
            (Induct { nparams = J.to_int (J.field "numParams" o); nindices = J.to_int (J.field "numIndices" o);
                      all = names (J.field "all" o); ctors = names (J.field "ctors" o);
                      nnested = J.to_int (J.field "numNested" o); is_rec = J.to_bool (J.field "isRec" o);
                      is_reflexive = J.to_bool (J.field "isReflexive" o) })
            (J.to_bool (J.field "isUnsafe" o)) in
        let ctor o = mk (name (J.field "name" o)) (names (J.field "levelParams" o)) (expr (J.field "type" o))
            (Ctor { induct = name (J.field "induct" o); cidx = J.to_int (J.field "cidx" o);
                    cnparams = J.to_int (J.field "numParams" o); nfields = J.to_int (J.field "numFields" o) })
            (J.to_bool (J.field "isUnsafe" o)) in
        let rule o = { r_ctor = name (J.field "ctor" o); r_nfields = J.to_int (J.field "nfields" o);
                       r_rhs = expr (J.field "rhs" o) } in
        let recr o = mk (name (J.field "name" o)) (names (J.field "levelParams" o)) (expr (J.field "type" o))
            (Rec { rall = names (J.field "all" o); rnparams = J.to_int (J.field "numParams" o);
                   rnindices = J.to_int (J.field "numIndices" o); nmotives = J.to_int (J.field "numMotives" o);
                   nminors = J.to_int (J.field "numMinors" o);
                   rules = List.map rule (J.to_list (J.field "rules" o)); k = J.to_bool (J.field "k" o) })
            (J.to_bool (J.field "isUnsafe" o)) in
        push (Rdecl.IndBlock { types = List.map ty (J.to_list (J.field "types" o));
                               ctors = List.map ctor (J.to_list (J.field "ctors" o));
                               recs = List.map recr (J.to_list (J.field "recs" o)) })
      end else if has "meta" then ()
      else bad "unknown line kind"
    | _ -> bad "line is not an object" in
  let lineno = ref 0 in
  (try
     while true do
       let l = input_line ic in
       incr lineno;
       if String.length l > 0 then
         (try
            (* a non-quot declaration line ends a quotient package *)
            line l
          with J.Error m -> bad "line %d: json error: %s" !lineno m
             | Bad m -> bad "line %d: %s" !lineno m
             | Failure m | Invalid_argument m -> bad "line %d: %s" !lineno m)
     done
   with End_of_file -> ());
  flush ();
  List.rev !blocks

let count_decls blocks =
  List.fold_left (fun a -> function
      | Rdecl.Single _ -> a + 1
      | Rdecl.QuotBlock l -> a + List.length l
      | Rdecl.IndBlock { types; ctors; recs } -> a + List.length types + List.length ctors + List.length recs) 0 blocks

let () =
  let file = ref "" and skip = ref false in
  Array.iteri (fun i a ->
      if i > 0 then begin
        if !skip then skip := false
        else if a = "-j" then skip := true
        else if String.length a > 0 && a.[0] = '-' && a <> "-" then ()
        else file := a
      end) Sys.argv;
  if !file = "" then (prerr_endline "usage: refcheck [-q] [-j N] FILE.ndjson"; exit 3);
  match parse_file !file with
  | exception Bad m -> Printf.printf "parse error: %s\n" m; exit 3
  | exception Sys_error m -> Printf.printf "error: %s\n" m; exit 3
  | blocks ->
    (* unsafe / partial definitions may see their mutual group *)
    List.iter (function
        | Rdecl.Single ({ kind = Defn { safety = (Unsafe | Partial); _ }; _ } as d) -> Hashtbl.replace Rdecl.forward d.name d
        | _ -> ()) blocks;
    (try
       List.iter Rdecl.check_block blocks;
       Printf.printf "accepted %d declarations\n" (count_decls blocks); exit 0
     with
     | Reject m -> Printf.printf "rejected: %s\n" m; exit 1
     | Too_complex m -> Printf.printf "error: %s\n" m; exit 3
     | Stack_overflow -> Printf.printf "error: stack overflow\n"; exit 3
     | Out_of_memory -> Printf.printf "error: out of memory\n"; exit 3
     | Stdlib.Exit -> exit 3
     | e -> Printf.printf "internal error: %s\n" (Printexc.to_string e); exit 3)
