(* Reader for the lean4export NDJSON format (version 3.x). *)
open Env
module J = Json

exception Bad of string
let bad fmt = Printf.ksprintf (fun s -> raise (Bad s)) fmt

type st = {
  names : (int, Name.t) Hashtbl.t;
  levels : (int, Level.t) Hashtbl.t;
  exprs : (int, Expr.t) Hashtbl.t;
  consts : (Name.t, cinfo) Hashtbl.t;
  mutable blocks : block list;
  mutable nblocks : int;
  mutable dups : Name.t list;
  mutable pending_quot : cinfo list;   (* consecutive quot lines *)
}

let get tbl i what = match Hashtbl.find_opt tbl i with
  | Some x -> x | None -> bad "undefined %s reference %d" what i

let name st j = get st.names (J.to_int j) "name"
let level st j = get st.levels (J.to_int j) "level"
let expr st j = get st.exprs (J.to_int j) "expr"
let names st j = List.map (name st) (J.to_list j)

let def_unique tbl i v what =
  if Hashtbl.mem tbl i then bad "duplicate %s index %d" what i;
  Hashtbl.replace tbl i v

let flush_quot st =
  match st.pending_quot with
  | [] -> ()
  | l ->
    let l = List.rev l in
    List.iter (fun c -> c.pos <- st.nblocks) l;
    st.blocks <- QuotBlock l :: st.blocks;
    st.nblocks <- st.nblocks + 1;
    st.pending_quot <- []

let add_block st b =
  flush_quot st;
  let pos = st.nblocks in
  let reg c =
    c.pos <- pos;
    if Hashtbl.mem st.consts c.name then st.dups <- c.name :: st.dups
    else Hashtbl.replace st.consts c.name c in
  (match b with
   | Single c -> reg c
   | QuotBlock l -> List.iter reg l
   | IndBlock { types; ctors; recs } -> List.iter reg types; List.iter reg ctors; List.iter reg recs);
  st.blocks <- b :: st.blocks;
  st.nblocks <- pos + 1

let mk name lparams ty kind unsafe = { name; lparams; ty; kind; unsafe; pos = -1 }

let line st (s : string) =
  let j = J.parse s in
  match j with
  | J.Obj fields ->
    let has k = List.mem_assoc k fields in
    let f k = List.assoc k fields in
    if has "in" then begin
      let i = J.to_int (f "in") in
      let n =
        if has "str" then let o = f "str" in Name.str (name st (J.field "pre" o)) (J.to_str (J.field "str" o))
        else if has "num" then let o = f "num" in Name.num (name st (J.field "pre" o)) (J.to_int (J.field "i" o))
        else bad "bad name line" in
      def_unique st.names i n "name"
    end else if has "il" then begin
      let i = J.to_int (f "il") in
      let l =
        if has "succ" then Level.succ (level st (f "succ"))
        else if has "max" then (match J.to_list (f "max") with
            | [a; b] -> Level.max_core (level st a) (level st b) | _ -> bad "bad max")
        else if has "imax" then (match J.to_list (f "imax") with
            | [a; b] -> Level.imax_core (level st a) (level st b) | _ -> bad "bad imax")
        else if has "param" then Level.param (name st (f "param"))
        else bad "bad level line" in
      def_unique st.levels i l "level"
    end else if has "ie" then begin
      let i = J.to_int (f "ie") in
      let e =
        if has "bvar" then Expr.bvar (J.to_int (f "bvar"))
        else if has "sort" then Expr.sort (level st (f "sort"))
        else if has "const" then
          let o = f "const" in
          Expr.const (name st (J.field "name" o)) (List.map (level st) (J.to_list (J.field "us" o)))
        else if has "app" then let o = f "app" in Expr.app (expr st (J.field "fn" o)) (expr st (J.field "arg" o))
        else if has "lam" then let o = f "lam" in Expr.lam (expr st (J.field "type" o)) (expr st (J.field "body" o))
        else if has "forallE" then let o = f "forallE" in Expr.pi (expr st (J.field "type" o)) (expr st (J.field "body" o))
        else if has "letE" then
          let o = f "letE" in
          Expr.let_ (expr st (J.field "type" o)) (expr st (J.field "value" o)) (expr st (J.field "body" o))
        else if has "proj" then
          let o = f "proj" in
          let idx = J.to_int (J.field "idx" o) in
          if idx < 0 then bad "negative projection index";
          Expr.proj (name st (J.field "typeName" o)) idx (expr st (J.field "struct" o))
        else if has "natVal" then
          (match f "natVal" with
           | J.Str s -> let z = Z.of_string s in if Z.sign z < 0 then bad "negative nat"; Expr.natlit z
           | J.Int n when n >= 0 -> Expr.natlit (Z.of_int n)
           | _ -> bad "bad natVal")
        else if has "strVal" then Expr.strlit (J.to_str (f "strVal"))
        else if has "mdata" then expr st (J.field "expr" (f "mdata"))
        else bad "bad expr line" in
      def_unique st.exprs i e "expr"
    end else if has "axiom" then begin
      let o = f "axiom" in
      add_block st (Single (mk (name st (J.field "name" o)) (names st (J.field "levelParams" o))
                              (expr st (J.field "type" o)) Axiom (J.to_bool (J.field "isUnsafe" o))))
    end else if has "def" then begin
      let o = f "def" in
      let hints = match J.field "hints" o with
        | J.Str "opaque" -> Opaque | J.Str "abbrev" -> Abbrev
        | J.Obj [ ("regular", J.Int h) ] -> Regular h
        | _ -> bad "bad hints" in
      let safety = match J.field "safety" o with
        | J.Str "safe" -> Safe | J.Str "unsafe" -> Unsafe | J.Str "partial" -> Partial
        | _ -> bad "bad safety" in
      add_block st (Single (mk (name st (J.field "name" o)) (names st (J.field "levelParams" o))
                              (expr st (J.field "type" o))
                              (Defn { value = expr st (J.field "value" o); hints; safety;
                                      all = names st (J.field "all" o) })
                              (safety = Unsafe)))
    end else if has "thm" then begin
      let o = f "thm" in
      add_block st (Single (mk (name st (J.field "name" o)) (names st (J.field "levelParams" o))
                              (expr st (J.field "type" o))
                              (Thm { value = expr st (J.field "value" o); all = names st (J.field "all" o) }) false))
    end else if has "opaque" then begin
      let o = f "opaque" in
      add_block st (Single (mk (name st (J.field "name" o)) (names st (J.field "levelParams" o))
                              (expr st (J.field "type" o))
                              (Opaq { value = expr st (J.field "value" o); all = names st (J.field "all" o) })
                              (J.to_bool (J.field "isUnsafe" o))))
    end else if has "quot" then begin
      let o = f "quot" in
      let k = match J.field "kind" o with
        | J.Str "type" -> QType | J.Str "ctor" -> QCtor | J.Str "lift" -> QLift | J.Str "ind" -> QInd
        | _ -> bad "bad quot kind" in
      let c = mk (name st (J.field "name" o)) (names st (J.field "levelParams" o)) (expr st (J.field "type" o)) (Quot k) false in
      if Hashtbl.mem st.consts c.name || List.exists (fun d -> Name.equal d.name c.name) st.pending_quot
      then st.dups <- c.name :: st.dups
      else Hashtbl.replace st.consts c.name c;
      st.pending_quot <- c :: st.pending_quot
    end else if has "inductive" then begin
      let o = f "inductive" in
      let ty o = mk (name st (J.field "name" o)) (names st (J.field "levelParams" o)) (expr st (J.field "type" o))
          (Induct { nparams = J.to_int (J.field "numParams" o); nindices = J.to_int (J.field "numIndices" o);
                    all = names st (J.field "all" o); ctors = names st (J.field "ctors" o);
                    nnested = J.to_int (J.field "numNested" o); is_rec = J.to_bool (J.field "isRec" o);
                    is_reflexive = J.to_bool (J.field "isReflexive" o) })
          (J.to_bool (J.field "isUnsafe" o)) in
      let ctor o = mk (name st (J.field "name" o)) (names st (J.field "levelParams" o)) (expr st (J.field "type" o))
          (Ctor { induct = name st (J.field "induct" o); cidx = J.to_int (J.field "cidx" o);
                  cnparams = J.to_int (J.field "numParams" o); nfields = J.to_int (J.field "numFields" o) })
          (J.to_bool (J.field "isUnsafe" o)) in
      let rule o = { r_ctor = name st (J.field "ctor" o); r_nfields = J.to_int (J.field "nfields" o);
                     r_rhs = expr st (J.field "rhs" o) } in
      let recr o = mk (name st (J.field "name" o)) (names st (J.field "levelParams" o)) (expr st (J.field "type" o))
          (Recursor { rall = names st (J.field "all" o); rnparams = J.to_int (J.field "numParams" o);
                      rnindices = J.to_int (J.field "numIndices" o); nmotives = J.to_int (J.field "numMotives" o);
                      nminors = J.to_int (J.field "numMinors" o);
                      rules = List.map rule (J.to_list (J.field "rules" o)); k = J.to_bool (J.field "k" o) })
          (J.to_bool (J.field "isUnsafe" o)) in
      add_block st (IndBlock { types = List.map ty (J.to_list (J.field "types" o));
                               ctors = List.map ctor (J.to_list (J.field "ctors" o));
                               recs = List.map recr (J.to_list (J.field "recs" o)) })
    end else if has "meta" then ()
    else bad "unknown line kind"
  | _ -> bad "line is not an object"

let read_channel ic : Env.t =
  let st = { names = Hashtbl.create 100_000; levels = Hashtbl.create 1000; exprs = Hashtbl.create 1_000_000;
             consts = Hashtbl.create 100_000; blocks = []; nblocks = 0; dups = []; pending_quot = [] } in
  Hashtbl.replace st.names 0 Name.Anon;
  Hashtbl.replace st.levels 0 Level.zero;
  let lineno = ref 0 in
  (try
     while true do
       let l = input_line ic in
       incr lineno;
       if String.length l > 0 then
         (try line st l with
          | J.Error m -> bad "line %d: json error: %s" !lineno m
          | Bad m -> bad "line %d: %s" !lineno m
          | Failure m | Invalid_argument m -> bad "line %d: %s" !lineno m)
     done
   with End_of_file -> ());
  flush_quot st;
  { consts = st.consts; blocks = Array.of_list (List.rev st.blocks); dups = st.dups }
