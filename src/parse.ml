(* Reader for the lean4export NDJSON format (version 3.x). *)
open Env
module J = Json

exception Bad of string
let bad fmt = Printf.ksprintf (fun s -> raise (Bad s)) fmt

(* index -> value tables: dense arrays, with a hash table for far-away indices *)
module Idx = struct
  (* Flat arrays holding values directly (no [option] box per entry), with a
     sentinel for "undefined"; far-away indices go to a hash table. *)
  type 'a t = { mutable arr : 'a array; sparse : (int, 'a) Hashtbl.t; none : 'a }
  let create none n = { arr = Array.make n none; sparse = Hashtbl.create 16; none }
  let find t i =
    if i >= 0 && i < Array.length t.arr then
      (let v = Array.unsafe_get t.arr i in if v == t.none then None else Some v)
    else Hashtbl.find_opt t.sparse i
  let mem t i =
    if i >= 0 && i < Array.length t.arr then Array.unsafe_get t.arr i != t.none
    else Hashtbl.mem t.sparse i
  let set t i v =
    if i < 0 then Hashtbl.replace t.sparse i v
    else begin
      if i >= Array.length t.arr && i < 4 * Array.length t.arr + 1_000_000 then begin
        let na = Array.make (max (3 * Array.length t.arr / 2) (i + 1)) t.none in
        Array.blit t.arr 0 na 0 (Array.length t.arr); t.arr <- na
      end;
      if i < Array.length t.arr then t.arr.(i) <- v else Hashtbl.replace t.sparse i v
    end
end

type st = {
  names : Name.t Idx.t;
  levels : Level.t Idx.t;
  exprs : Expr.t Idx.t;
  fl : Fastline.st;
  consts : cinfo Name.Tbl.t;
  mutable blocks : block list;
  mutable nblocks : int;
  mutable dups : Name.t list;
  mutable pending_quot : cinfo list;   (* consecutive quot lines *)
}

let get tbl i what = match Idx.find tbl i with
  | Some x -> x | None -> bad "undefined %s reference %d" what i

let name st j = get st.names (J.to_int j) "name"
let level st j = get st.levels (J.to_int j) "level"
let expr st j = get st.exprs (J.to_int j) "expr"
let names st j = List.map (name st) (J.to_list j)

let def_unique tbl i v what =
  if Idx.mem tbl i then bad "duplicate %s index %d" what i;
  Idx.set tbl i v

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
    if Name.Tbl.mem st.consts c.name then st.dups <- c.name :: st.dups
    else Name.Tbl.replace st.consts c.name c in
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
      if Name.Tbl.mem st.consts c.name || List.exists (fun d -> Name.equal d.name c.name) st.pending_quot
      then st.dups <- c.name :: st.dups
      else Name.Tbl.replace st.consts c.name c;
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

(* fast path for name / level / expression lines *)
(* build the entry of a line already scanned into [st.fl]; false: not handled *)
let rec fast_line st (l : Bytes.t) start stop : bool =
  Fastline.scan st.fl l start stop && fast_build st l
and fast_build st (l : Bytes.t) : bool =
  let f = st.fl in
  begin
    let open Fastline in
    let iv k = f.ints.(k) in
    let has k = f.ints.(k) <> min_int in
    let sv k = if f.slen.(k) < 0 then raise Exit else Bytes.sub_string l f.sstart.(k) f.slen.(k) in
    let nm k = get st.names (iv k) "name" and lv k = get st.levels (iv k) "level" and ex k = get st.exprs (iv k) "expr" in
    try
      if has k_ie then begin
        let i = iv k_ie in
        let e =
          if has k_bvar then Expr.bvar (iv k_bvar)
          else if has k_sort then Expr.sort (lv k_sort)
          else if f.kind = k_app then Expr.app (ex k_fn) (ex k_arg)
          else if f.kind = k_const then begin
            if f.arr_key <> k_us then raise Exit;
            let ls = List.init f.arr_n (fun j -> get st.levels f.arr.(j) "level") in
            Expr.const (nm k_name) ls
          end
          else if f.kind = k_forall then Expr.pi (ex k_type) (ex k_body)
          else if f.kind = k_lam then Expr.lam (ex k_type) (ex k_body)
          else if f.kind = k_let then Expr.let_ (ex k_type) (ex k_value) (ex k_body)
          else if f.kind = k_proj then
            (if iv k_idx < 0 then raise Exit; Expr.proj (nm k_typename) (iv k_idx) (ex k_struct))
          else if f.slen.(k_strval) >= 0 then raise Exit   (* may contain escapes: generic path *)
          else if f.slen.(k_natval) >= 0 then Expr.natlit (Z.of_string (sv k_natval))
          else raise Exit in
        def_unique st.exprs i e "expr"; true
      end else if has k_in then begin
        let i = iv k_in in
        let n =
          if f.kind = k_str then Name.str (nm k_pre) (sv k_str)
          else if f.kind = k_num then Name.num (nm k_pre) (iv k_i)
          else raise Exit in
        def_unique st.names i n "name"; true
      end else if has k_il then begin
        let i = iv k_il in
        let l =
          if has k_succ then Level.succ (lv k_succ)
          else if has k_param then Level.param (nm k_param)
          else if f.arr_n = 2 && f.arr_key = k_max then
            Level.max_core (get st.levels f.arr.(0) "level") (get st.levels f.arr.(1) "level")
          else if f.arr_n = 2 && f.arr_key = k_imax then
            Level.imax_core (get st.levels f.arr.(0) "level") (get st.levels f.arr.(1) "level")
          else raise Exit in
        def_unique st.levels i l "level"; true
      end else false
    with Exit -> false
  end

(* [size_hint]: input size in bytes (0 if unknown).  Exports average 55-60
   bytes per line and about 90% of lines are expressions, so tables can be
   allocated at their final size instead of growing by copying. *)
let read_channel ?(size_hint = 0) ic : Env.t =
  let est_lines = size_hint / 52 in
  (* sentinels: fresh values that no parsed entry can be physically equal to *)
  let st = { names = Idx.create (Name.Str { h = 0; pre = Name.Anon; s = "<undefined>" }) 100_000;
             levels = Idx.create (Level.Param { h = 0; n = Name.Anon }) 1000;
             exprs = Idx.create (Expr.BVar { hi = 0; idx = -1 }) (max 1_000_000 est_lines); fl = Fastline.create ();
             consts = Name.Tbl.create 100_000; blocks = []; nblocks = 0; dups = []; pending_quot = [] } in
  Idx.set st.names 0 Name.Anon;
  Idx.set st.levels 0 Level.zero;
  let lineno = ref 0 in
  (* Lines are scanned in place in a large buffer refilled with [input]: one
     channel operation (and lock) per megabyte instead of per line, and no
     string allocated for lines the fast path handles. *)
  let buf = ref (Bytes.create (1 lsl 20)) in
  let lo = ref 0 and hi = ref 0 and eof = ref false in
  let refill () =
    (* keep the unfinished line, at the front; grow for very long lines *)
    let rem = !hi - !lo in
    if rem = Bytes.length !buf then begin
      let nb = Bytes.create (2 * Bytes.length !buf) in
      Bytes.blit !buf !lo nb 0 rem; buf := nb
    end else Bytes.blit !buf !lo !buf 0 rem;
    lo := 0; hi := rem;
    let k = input ic !buf !hi (Bytes.length !buf - !hi) in
    if k = 0 then eof := true else hi := !hi + k in
  let handle ?(scanned = false) start stop =
    incr lineno;
    let b = !buf in
    if stop > start then
      (try
         let ok = if scanned then fast_build st b else fast_line st b start stop in
         if not ok then line st (Bytes.sub_string b start (stop - start)) with
       | J.Error m -> bad "line %d: json error: %s" !lineno m
       | Bad m -> bad "line %d: %s" !lineno m
       | Failure m | Invalid_argument m -> bad "line %d: %s" !lineno m) in
  let rec next () =
    let b = !buf and h = !hi in
    (* fast path: scanning the object finds the end of the line, so the bytes
       are read once; otherwise search for the newline *)
    let e = Fastline.scan_prefix st.fl b !lo h in
    if e >= 0 && e < h && Bytes.unsafe_get b e = '\n' then begin
      let start = !lo in lo := e + 1; handle ~scanned:true start e; next ()
    end else
    let i = ref !lo in
    while !i < h && Bytes.unsafe_get b !i <> '\n' do incr i done;
    if !i < h then (let start = !lo in lo := !i + 1; handle start !i; next ())
    else if !eof then (if h > !lo then (let start = !lo in lo := h; handle start h))
    else (refill (); next ()) in
  next ();
  flush_quot st;
  { consts = st.consts; blocks = Array.of_list (List.rev st.blocks); dups = st.dups }
