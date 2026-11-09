(* NbE checker for declaration values over integer handles (prototype, step 3).

   The same algorithm as Nbe (closures, lazy spines, bidirectional checking,
   Tc.is_def_eq's conversion heuristics), with a different representation:
   values, thunks, environments, heads and constants are integer ids into
   flat Bigarray storage that the GC does not scan.  The storage belongs to
   the domain and is reused: each declaration starts a new epoch, which
   resets allocation counters and invalidates every intern-table entry at
   no cost.  The only OCaml pointers kept are in side arrays: terms, levels,
   names and literals, mostly old objects of the environment.

   Interned (so that equal things are the same id and the in-place caches
   hit): thunks by (term, substitution, environment) -- the evaluation memo --
   environments by (thunk, tail), neutrals by (head, spine), constants by
   (name, levels), projection heads.  Binders are not interned (on Init the
   binder table had 55 hits for 63 M inserts, docs/NBE.md).  Neutrals carry
   their whnf_core, whnf, type and unfolding as int fields.

   Trust model as in Nbe: [check_decl] returns or raises, and the caller
   re-checks with Tc on any exception, so every rejection is Tc's. *)
open Expr
open Env

exception Decline = Nbe.Decline
let decline s = raise (Decline s)
let fail = Tc.fail

(* ------------------------------------------------------------ storage *)
module A1 = Bigarray.Array1
type col = (int, Bigarray.int_elt, Bigarray.c_layout) A1.t
let col_make n : col = let a = A1.create Bigarray.int Bigarray.c_layout n in A1.fill a 0; a

(* records of [stride] ints; id 0 is reserved *)
type ar = { mutable d : col; mutable n : int; stride : int }
let ar_make stride cap = { d = col_make (stride * cap); n = 1; stride }
let ar_grow a =
  let old = a.d in
  let nd = col_make (2 * A1.dim old) in
  A1.blit old (A1.sub nd 0 (A1.dim old)); a.d <- nd
let[@inline] ar_new a =
  if (a.n + 1) * a.stride > A1.dim a.d then ar_grow a;
  let id = a.n in a.n <- id + 1; id
let[@inline] g (a : ar) id f = A1.unsafe_get a.d (id * a.stride + f)
let[@inline] p (a : ar) id f v = A1.unsafe_set a.d (id * a.stride + f) v

(* OCaml values indexed like an [ar] *)
type 'a side = { mutable sa : 'a array; dflt : 'a }
let side_make d cap = { sa = Array.make cap d; dflt = d }
let side_set s i x =
  if i >= Array.length s.sa then begin
    let na = Array.make (2 * Array.length s.sa + i) s.dflt in
    Array.blit s.sa 0 na 0 (Array.length s.sa); s.sa <- na
  end;
  Array.unsafe_set s.sa i x
let[@inline] side_get s i = Array.unsafe_get s.sa i

(* Open-addressing intern table from a hash to an id.  A slot is one word:
   [epoch (15 bits) | hash tag (16 bits) | id (32 bits)], 0 = empty.  Slots
   of older epochs read as empty, so starting a new epoch empties the table;
   within an epoch nothing is deleted, so a probe can stop at the first
   empty or stale slot.  One array per table: a probe is one memory access,
   and the record is read only when the tag matches.  Growing recomputes the
   hashes of the current entries with [rehash]. *)
type itab = { mutable sl : col; mutable mask : int; mutable cnt : int; mutable ep : int;
              mutable rehash : int -> int }

let itab_make cap = { sl = col_make cap; mask = cap - 1; cnt = 0; ep = 1; rehash = (fun _ -> 0) }

(* A table keeps the size its largest declaration needed; a big sparse table
   costs a cache miss per lookup, so a table over a million slots that the
   last declaration used to less than 1/64 is reallocated small. *)
let itab_small = 1 lsl 12
let itab_reset t ep clear =
  if t.mask + 1 > (1 lsl 20) && t.cnt < (t.mask + 1) / 64 then begin
    t.sl <- col_make itab_small; t.mask <- itab_small - 1
  end else if clear then A1.fill t.sl 0;
  t.cnt <- 0; t.ep <- ep

(* MurmurHash3's 64-bit finalizer (on 63-bit ints): keys are small
   sequential ids, which Hc.mix (a multiply by 0x100000001b3) spreads poorly *)
let[@inline] fmix h =
  let h = h lxor (h lsr 33) in
  let h = h * 0x3f51afd7ed558ccd in
  let h = h lxor (h lsr 33) in
  let h = h * 0x44ceb9fe1a85ec53 in
  h lxor (h lsr 33)
let[@inline] mix3 a b c = (fmix (a lxor fmix (b lxor fmix (c + 0x2545F491)))) land max_int

let[@inline] tag_of h = (h lsr 40) land 0xFFFF
let[@inline] live x ep = x <> 0 && x lsr 48 = ep
let[@inline] slot_id x = x land 0xFFFFFFFF

let itab_find t h (eq : int -> bool) =
  let sl = t.sl and mask = t.mask and ep = t.ep and tg = tag_of h in
  let rec go i =
    let x = A1.unsafe_get sl i in
    if not (live x ep) then 0
    else if (x lsr 32) land 0xFFFF = tg && eq (slot_id x) then slot_id x
    else go ((i + 1) land mask) in
  go (h land mask)

let rec itab_slot sl mask ep i =
  if live (A1.unsafe_get sl i) ep then itab_slot sl mask ep ((i + 1) land mask) else i

let itab_add t h id =
  if 2 * (t.cnt + 1) > t.mask + 1 then begin
    let cap = 2 * (t.mask + 1) in
    let sl = col_make cap in
    for i = 0 to t.mask do
      let x = A1.unsafe_get t.sl i in
      if live x t.ep then begin
        let j = itab_slot sl (cap - 1) t.ep (t.rehash (slot_id x) land (cap - 1)) in
        A1.unsafe_set sl j x
      end
    done;
    t.sl <- sl; t.mask <- cap - 1
  end;
  let j = itab_slot t.sl t.mask t.ep (h land t.mask) in
  A1.unsafe_set t.sl j ((t.ep lsl 48) lor (tag_of h lsl 32) lor id);
  t.cnt <- t.cnt + 1

(* ------------------------------------------------------------- layouts *)
(* values (stride 9): kind, a, b, c, open, whnf_c, whnf_f, ty, unf *)
let k_sort = 1 and k_pi = 2 and k_lam = 3 and k_neu = 4 and k_nat = 5 and k_str = 6
(* Sort: level in vlev.  Pi/Lam: a = domain thunk, b = substitution,
   c = environment, body in vexp.  Neu: a = head, b = spine (environment,
   last argument first), c = number of arguments.  Nat/Str: vz / vs. *)
let f_kind = 0 and f_a = 1 and f_b = 2 and f_c = 3 and f_open = 4
and f_wc = 5 and f_wf = 6 and f_ty = 7 and f_unf = 8
(* thunks (stride 4): substitution, environment, value (0 = unforced), open;
   the term in texp (a forced-value thunk has [dontcare]) *)
(* environments (stride 4): thunk, tail, length, open; env 0 is empty *)
(* heads (stride 4): kind, a, b, open.  Const: a = constant entry.
   Local: a = type.  Proj: a = field, b = structure value, name in hname. *)
let h_const = 1 and h_local = 2 and h_proj = 3
(* constant entries (stride 4): head, substitution (0 or the entry itself),
   delta value (0 unknown, -1 none), type (0 unknown); name and levels in
   cname / clev, substitution parameters in sps *)
(* pairs (stride 2) for the success / failure caches *)
(* inference memo entries (stride 2): context id, type; term in infe *)

type st = {
  mutable tc : Tc.ctx;
  mutable fuel : int;
  mutable eager : bool;
  mutable rdepth : int;
  mutable epoch : int;
  mutable ncx : int;
  counts : int array;
  v : ar; vexp : Expr.t side; vlev : Level.t side; vz : Z.t side; vs : string side;
  t : ar; texp : Expr.t side;
  e : ar;
  h : ar; hname : Name.t side;
  c : ar; cname : Name.t side; clev : Level.t list side; sps : Name.t list side;
  cinfo : cinfo option side;           (* Tc.find of the name, looked up once *)
  pr : ar;
  inf : ar; infe : Expr.t side;
  tab_t : itab; tab_vt : itab; tab_e : itab; tab_n : itab; tab_c : itab; tab_p : itab;
  tab_inf : itab; tab_succ : itab; tab_fail : itab;
}

let ncounters = Array.length Nbe.counter_names
let cnt st i = if Nbe.stats_on then st.counts.(i) <- st.counts.(i) + 1

let make () =
  let cap = 1 lsl 12 in
  { tc = Obj.magic 0; fuel = 0; eager = false; rdepth = 0; epoch = 1; ncx = 0;
    counts = Array.make ncounters 0;
    v = ar_make 9 cap; vexp = side_make Tc.dontcare cap; vlev = side_make Level.zero 16;
    vz = side_make Z.zero 16; vs = side_make "" 16;
    t = ar_make 4 cap; texp = side_make Tc.dontcare cap;
    e = ar_make 4 cap;
    h = ar_make 4 cap; hname = side_make Name.Anon 16;
    c = ar_make 4 256; cname = side_make Name.Anon 256; clev = side_make [] 256; sps = side_make [] 256; cinfo = side_make None 256;
    pr = ar_make 2 256;
    inf = ar_make 2 256; infe = side_make Tc.dontcare 256;
    tab_t = itab_make cap; tab_vt = itab_make 256; tab_e = itab_make cap; tab_n = itab_make cap;
    tab_c = itab_make 256; tab_p = itab_make 256; tab_inf = itab_make 256;
    tab_succ = itab_make 256; tab_fail = itab_make 256 }

let reset st (tc : Tc.ctx) =
  st.tc <- tc; st.fuel <- Nbe.fuel; st.eager <- false; st.rdepth <- 0; st.ncx <- 0;
  st.epoch <- st.epoch + 1;
  let clear = st.epoch >= 1 lsl 15 in
  if clear then st.epoch <- 1;
  Array.fill st.counts 0 ncounters 0;
  List.iter (fun a -> a.n <- 1) [st.v; st.t; st.e; st.h; st.c; st.pr; st.inf];
  (* the empty environment and the identity substitution are id 0 *)
  for f = 0 to 3 do p st.e 0 f 0 done;
  List.iter (fun t -> itab_reset t st.epoch clear)
    [st.tab_t; st.tab_vt; st.tab_e; st.tab_n; st.tab_c; st.tab_p; st.tab_inf; st.tab_succ; st.tab_fail]

let make_st () =
  let st = make () in
  st.tab_e.rehash <- (fun x -> mix3 (g st.e x 0) (g st.e x 1) 1);
  st.tab_vt.rehash <- (fun x -> mix3 (g st.t x 2) 0 2);
  st.tab_t.rehash <- (fun x -> mix3 (Expr.hash (side_get st.texp x)) (g st.t x 0) (g st.t x 1));
  st.tab_n.rehash <- (fun v -> mix3 (g st.v v 1) (g st.v v 2) 3);
  st.tab_c.rehash <- (fun x -> mix3 (Name.hash (side_get st.cname x))
                                 (List.fold_left (fun h l -> Hc.mix h (Level.hash l)) 17 (side_get st.clev x)) 4);
  st.tab_p.rehash <- (fun x -> mix3 (Name.hash (side_get st.hname x)) (g st.h x 1) (g st.h x 2));
  st.tab_inf.rehash <- (fun x -> mix3 (Expr.hash (side_get st.infe x)) (g st.inf x 0) 6);
  st.tab_succ.rehash <- (fun x -> mix3 (g st.pr x 0) (g st.pr x 1) 5);
  st.tab_fail.rehash <- st.tab_succ.rehash;
  st

let key = Domain.DLS.new_key make_st

let tick st = st.fuel <- st.fuel - 1; if st.fuel <= 0 then decline "fuel"

(* O4L_NBH_INTERN=1 interns environments, neutrals and open thunks; by
   default only closed terms (size >= Nbe.memo_size) are memoised, as in Nbe
   (interning cost more in lookups than it saved on Init, docs/NBE.md) *)
let intern = Sys.getenv_opt "O4L_NBH_INTERN" = Some "1"
(* storage is not reclaimed within a declaration: past this many values the
   declaration is left to Tc *)
let max_values = match Sys.getenv_opt "O4L_NBH_MAX_VALUES" with Some v -> int_of_string v | None -> 4_000_000
let enter st = st.rdepth <- st.rdepth + 1; if st.rdepth > Nbe.max_depth then decline "recursion depth"
let leave st = st.rdepth <- st.rdepth - 1

(* -------------------------------------------------------------- values *)
let[@inline] kind st v = g st.v v f_kind
let[@inline] vopen st v = g st.v v f_open = 1

let new_value st k a b c op =
  let v = ar_new st.v in
  if v > max_values then decline "value storage";
  p st.v v f_kind k; p st.v v f_a a; p st.v v f_b b; p st.v v f_c c; p st.v v f_open (if op then 1 else 0);
  p st.v v f_wc 0; p st.v v f_wf 0; p st.v v f_ty 0; p st.v v f_unf 0;
  v

let mk_sort st l = let v = new_value st k_sort 0 0 0 false in side_set st.vlev v l; v
let mk_nat st z = let v = new_value st k_nat 0 0 0 false in side_set st.vz v z; v
let mk_str st s = let v = new_value st k_str 0 0 0 false in side_set st.vs v s; v

(* environments *)
let[@inline] e_head st e = g st.e e 0
let[@inline] e_tail st e = g st.e e 1
let[@inline] e_len st e = g st.e e 2
let[@inline] e_open st e = g st.e e 3 = 1
let[@inline] t_open st t = g st.t t 3 = 1

(* the hot lookups are written out (no closure per call) *)
let find_env st th env h =
  let t = st.tab_e in
  let sl = t.sl and mask = t.mask and ep = t.ep and tg = tag_of h in
  let rec go i =
    let x = A1.unsafe_get sl i in
    if not (live x ep) then 0
    else if (x lsr 32) land 0xFFFF = tg && (let y = slot_id x in g st.e y 0 = th && g st.e y 1 = env) then slot_id x
    else go ((i + 1) land mask) in
  go (h land mask)

let cap_check (a : ar) = if a.n > 2 * max_values then decline "storage"

let push st env th =
  let h = if intern then mix3 th env 1 else 0 in
  let r = if intern then find_env st th env h else 0 in
  if r <> 0 then r
  else begin
    cap_check st.e;
    let x = ar_new st.e in
    p st.e x 0 th; p st.e x 1 env; p st.e x 2 (e_len st env + 1);
    p st.e x 3 (if e_open st env || t_open st th then 1 else 0);
    if intern then itab_add st.tab_e h x; x
  end

let rec nth_thunk st env i =
  if env = 0 then fail "type checker does not support loose bound variables"
  else if i = 0 then e_head st env else nth_thunk st (e_tail st env) (i - 1)

(* thunks of values *)
let of_value st v =
  let h = mix3 v 0 2 in
  let r = if intern then itab_find st.tab_vt h (fun x -> g st.t x 2 = v) else 0 in
  if r <> 0 then r
  else begin
    let x = ar_new st.t in
    p st.t x 0 0; p st.t x 1 0; p st.t x 2 v; p st.t x 3 (if vopen st v then 1 else 0);
    if intern then itab_add st.tab_vt h x; x
  end

(* heads and neutrals *)
let[@inline] h_kind st x = g st.h x 0
let[@inline] h_open st x = g st.h x 3 = 1

let find_neu st head spine h =
  let t = st.tab_n in
  let sl = t.sl and mask = t.mask and ep = t.ep and tg = tag_of h in
  let rec go i =
    let x = A1.unsafe_get sl i in
    if not (live x ep) then 0
    else if (x lsr 32) land 0xFFFF = tg && (let y = slot_id x in g st.v y f_a = head && g st.v y f_b = spine) then slot_id x
    else go ((i + 1) land mask) in
  go (h land mask)

let mk_neu st head spine nargs =
  let h = if intern then mix3 head spine 3 else 0 in
  let r = if intern then find_neu st head spine h else 0 in
  if r <> 0 then r
  else begin
    cnt st 1;
    let v = new_value st k_neu head spine nargs (h_open st head || e_open st spine) in
    if intern then itab_add st.tab_n h v; v
  end

let fresh_local st ty =
  let x = ar_new st.h in
  p st.h x 0 h_local; p st.h x 1 ty; p st.h x 2 0; p st.h x 3 1;
  mk_neu st x 0 0

let proj_head st s i sv =
  let h = mix3 (Name.hash s) i sv in
  let r = if not intern then 0 else itab_find st.tab_p h (fun x -> g st.h x 1 = i && g st.h x 2 = sv && Name.equal (side_get st.hname x) s) in
  if r <> 0 then r
  else begin
    let x = ar_new st.h in
    p st.h x 0 h_proj; p st.h x 1 i; p st.h x 2 sv; p st.h x 3 (if vopen st sv then 1 else 0);
    side_set st.hname x s;
    if intern then itab_add st.tab_p h x; x
  end

let mk_proj st s i sv = mk_neu st (proj_head st s i sv) 0 0

(* constant entries: one per (name, levels) *)
let levels_hash ls = List.fold_left (fun h l -> Hc.mix h (Level.hash l)) 17 ls
let rec levels_phys a b = match a, b with
  | x :: r, y :: s -> x == y && levels_phys r s
  | [], [] -> true
  | _ -> false

let const_entry st n ls =
  let h = mix3 (Name.hash n) (levels_hash ls) 4 in
  let r = itab_find st.tab_c h (fun x ->
      let m = side_get st.cname x in (m == n || Name.equal m n) && levels_phys (side_get st.clev x) ls) in
  if r <> 0 then r
  else begin
    let x = ar_new st.c in
    side_set st.cname x n; side_set st.clev x ls; side_set st.cinfo x (Tc.find st.tc n);
    let hd = ar_new st.h in
    p st.h hd 0 h_const; p st.h hd 1 x; p st.h hd 2 0; p st.h hd 3 0;
    p st.c x 0 hd; p st.c x 1 (-1); p st.c x 2 0; p st.c x 3 0;
    itab_add st.tab_c h x; x
  end

let const_val st n ls = mk_neu st (g st.c (const_entry st n ls) 0) 0 0

(* the substitution of a constant entry: its universe parameters := its levels *)
let sub_of st ce (ci : cinfo) =
  let s = g st.c ce 1 in
  if s >= 0 then s
  else begin
    let s = match ci.lparams with [] -> 0 | ps -> side_set st.sps ce ps; ce in
    p st.c ce 1 s; s
  end

let inst_level st sub l = if sub = 0 then l else Level.instantiate (side_get st.sps sub) (side_get st.clev sub) l
let inst_levels st sub ls = if sub = 0 then ls else List.map (inst_level st sub) ls

(* ---------------------------------------------------------- evaluation *)
let find_thunk st e sub env h =
  let t = st.tab_t in
  let sl = t.sl and mask = t.mask and ep = t.ep and tg = tag_of h in
  let rec go i =
    let x = A1.unsafe_get sl i in
    if not (live x ep) then 0
    else if (x lsr 32) land 0xFFFF = tg
         && (let y = slot_id x in side_get st.texp y == e && g st.t y 0 = sub && g st.t y 1 = env) then slot_id x
    else go ((i + 1) land mask) in
  go (h land mask)

let rec eval st env sub e =
  match e with
  | BVar { idx; _ } -> force st (nth_thunk st env idx)
  | NatLit { n; _ } -> mk_nat st n
  | StrLit { s; _ } -> mk_str st s
  | FVar _ -> decline "free variable"
  | Sort { l; _ } -> mk_sort st (inst_level st sub l)
  | Const { n; ls; _ } -> const_val st n (inst_levels st sub ls)
  | _ -> force st (mk_thunk st env sub e)

and eval_node st env sub e =
  cnt st 0;
  match e with
  | App _ ->
    let f, args = get_app_args e in
    let fv = eval st env sub f in
    if kind st fv = k_neu then begin
      let sp = ref (g st.v fv f_b) in
      Array.iter (fun a -> sp := push st !sp (mk_thunk st env sub a)) args;
      mk_neu st (g st.v fv f_a) !sp (g st.v fv f_c + Array.length args)
    end else Array.fold_left (fun v a -> apply st v (mk_thunk st env sub a)) fv args
  | Lam { ty; b; _ } -> mk_bnd st k_lam (mk_thunk st env sub ty) sub env b
  | Pi { ty; b; _ } -> mk_bnd st k_pi (mk_thunk st env sub ty) sub env b
  | Let { v; b; _ } -> eval st (push st env (mk_thunk st env sub v)) sub b
  | Proj { s; idx; e = se; _ } -> mk_proj st s idx (eval st env sub se)
  | _ -> eval st env sub e

and mk_bnd st k dom sub env body =
  let v = new_value st k dom sub env (t_open st dom || e_open st env) in
  side_set st.vexp v body; v

and mk_thunk st env sub e =
  match e with
  | BVar { idx; _ } -> nth_thunk st env idx
  | NatLit { n; _ } -> of_value st (mk_nat st n)
  | _ ->
    let c = closed e in
    let env = if c then 0 else env in
    let memo = intern || (c && size e >= Nbe.memo_size) in
    let h = if memo then mix3 (Expr.hash e) sub env else 0 in
    let r = if memo then find_thunk st e sub env h else 0 in
    if r <> 0 then r
    else begin
      cnt st 2;
      cap_check st.t;
      let x = ar_new st.t in
      p st.t x 0 sub; p st.t x 1 env; p st.t x 2 0; p st.t x 3 (if e_open st env then 1 else 0);
      side_set st.texp x e;
      if memo then itab_add st.tab_t h x; x
    end

and force st th =
  let v = g st.t th 2 in
  if v <> 0 then v
  else begin
    cnt st 3;
    let v = eval_node st (g st.t th 1) (g st.t th 0) (side_get st.texp th) in
    p st.t th 2 v; v
  end

and apply st v a =
  let k = kind st v in
  if k = k_lam then eval st (push st (g st.v v f_c) a) (g st.v v f_b) (side_get st.vexp v)
  else if k = k_neu then mk_neu st (g st.v v f_a) (push st (g st.v v f_b) a) (g st.v v f_c + 1)
  else decline "application of a non-function"

(* instantiate the codomain / body of a binder value *)
let inst_thunk st b th = eval st (push st (g st.v b f_c) th) (g st.v b f_b) (side_get st.vexp b)
let inst st b x = inst_thunk st b (of_value st x)
let dom st b = force st (g st.v b f_a)

(* the arguments of a neutral, in order *)
let args_array st n =
  let len = g st.v n f_c in
  let a = Array.make len 0 in
  let rec go e i = if i >= 0 then (a.(i) <- e_head st e; go (e_tail st e) (i - 1)) in
  go (g st.v n f_b) (len - 1); a

let apply_range st v args lo hi =
  let r = ref v in
  for i = lo to hi - 1 do r := apply st !r args.(i) done;
  !r

let apply_spine st v n =
  let rec go e = if e = 0 then v else apply st (go (e_tail st e)) (e_head st e) in
  go (g st.v n f_b)

let mk_app st head (args : int list) =
  let sp = List.fold_left (push st) 0 args in
  mk_neu st head sp (List.length args)

(* --------------------------------------------------------- environment *)
let find st n = Tc.find st.tc n
let get st n = Tc.get st.tc n

(* the constant at the head of a neutral, if any: (entry, name, levels) *)
let[@inline] neu_const st v =
  if kind st v <> k_neu then 0
  else let hd = g st.v v f_a in if h_kind st hd = h_const then g st.h hd 1 else 0

let const_type st ce =
  let t = g st.c ce 3 in
  if t <> 0 then t
  else begin
    let n = side_get st.cname ce in
    let ci = get st n in
    if List.compare_lengths ci.lparams (side_get st.clev ce) <> 0 then
      fail "incorrect number of universe levels for '%s'" (Name.to_string n);
    let t = eval st 0 (sub_of st ce ci) ci.ty in
    p st.c ce 3 t; t
  end

let delta_info st v =
  let ce = neu_const st v in
  if ce = 0 then None
  else match side_get st.cinfo ce with
    | Some ci when has_value ci && List.compare_lengths (side_get st.clev ce) ci.lparams = 0 -> Some ci
    | _ -> None

let delta_value st ce (ci : cinfo) =
  let d = g st.c ce 2 in
  if d > 0 then d
  else begin
    let body = match value ci with Some b -> b | None -> assert false in
    let d = eval st 0 (sub_of st ce ci) body in
    p st.c ce 2 d; d
  end

(* the neutral's unfolding, cached in place (0 unknown, -1 none) *)
let unfold st v =
  if kind st v <> k_neu then None
  else begin
    let u = g st.v v f_unf in
    if u > 0 then (cnt st 13; Some u)
    else if u < 0 then None
    else match delta_info st v with
      | Some ci ->
        cnt st 8;
        let r = apply_spine st (delta_value st (neu_const st v) ci) v in
        p st.v v f_unf r; Some r
      | None -> p st.v v f_unf (-1); None
  end

let ctor_of st v =
  let ce = neu_const st v in
  if ce = 0 then None
  else match side_get st.cinfo ce with
    | Some { kind = Ctor cv; _ } -> Some (ce, cv)
    | _ -> None

let is_const_name st v name =
  let ce = neu_const st v in ce <> 0 && (let n = side_get st.cname ce in n == name || Name.equal n name)

let nat_type st = const_val st Tc.N.nat []
let string_type st = const_val st Tc.N.string []
let nat_to_ctor st z =
  if Z.equal z Z.zero then const_val st Tc.N.nat_zero []
  else apply st (const_val st Tc.N.nat_succ []) (of_value st (mk_nat st (Z.pred z)))
let string_to_ctor st s = eval st 0 0 (Tc.string_lit_to_constructor s)

let[@inline] nargs st v = g st.v v f_c
let last_arg st v = e_head st (g st.v v f_b)

(* ----------------------------------------------------------- reduction *)
let rec whnf_core ?(cheap = false) st v =
  if kind st v <> k_neu then v
  else begin
    let m = g st.v v f_wc in
    if (not cheap) && m <> 0 then m
    else begin
      cnt st 7;
      let hd = g st.v v f_a in
      let hk = h_kind st hd in
      let r =
        if hk = h_local then v
        else if hk = h_proj then begin
          let sv = g st.h hd 2 in
          let sv' = if cheap then whnf_core ~cheap st sv else whnf st sv in
          match proj_reduce st (side_get st.hname hd) (g st.h hd 1) sv' with
          | Some fld -> whnf_core ~cheap st (apply_spine st fld v)
          | None -> v
        end else begin
          let ce = g st.h hd 1 in
          match reduce_rec st v ce (side_get st.clev ce) with
          | Some r -> whnf_core ~cheap st r
          | None -> v
        end in
      if not cheap then p st.v v f_wc r;
      r
    end
  end

and proj_reduce st sname idx sv =
  let sv = if kind st sv = k_str then whnf st (string_to_ctor st (side_get st.vs sv)) else sv in
  match ctor_of st sv with
  | Some (_, cv) when Name.equal cv.induct sname ->
    if cv.cnparams + idx < nargs st sv then Some (force st (args_array st sv).(cv.cnparams + idx)) else None
  | _ -> None

and reduce_rec st n ce ls =
  match side_get st.cinfo ce with
  | Some ({ kind = Quot (QLift | QInd); _ } as ci) when st.tc.Tc.bi.quot_ok -> quot_reduce st ci n
  | Some ({ kind = Recursor r; _ } as ci) -> iota st ci r ls n
  | _ -> None

and quot_reduce st ci n =
  let mk_pos, arg_pos = match ci.kind with Quot QLift -> 5, 3 | _ -> 4, 3 in
  if nargs st n <= mk_pos then None else begin
    let args = args_array st n in
    let mk = whnf st (force st args.(mk_pos)) in
    let ce = neu_const st mk in
    if ce <> 0 && nargs st mk = 3
       && (match side_get st.cinfo ce with Some { kind = Quot QCtor; _ } -> true | _ -> false) then begin
      let r = apply st (force st args.(arg_pos)) (last_arg st mk) in
      Some (apply_range st r args (mk_pos + 1) (nargs st n))
    end else None
  end

and iota st ci r ls n =
  cnt st 11;
  let { rnparams = nparams; nmotives; nminors; rnindices = nindices; rules; k; _ } = r in
  let major_idx = nparams + nmotives + nminors + nindices in
  let na = nargs st n in
  if major_idx >= na then None else begin
    let args = args_array st n in
    let induct = Tc.major_induct st.tc ci (nparams, nmotives, nminors, nindices) in
    let major = force st args.(major_idx) in
    let major = match k, induct with
      | true, Some ind -> to_ctor_when_k st ind major nparams
      | _ -> major in
    let major = whnf st major in
    let major =
      let mk = kind st major in
      if mk = k_nat then nat_to_ctor st (side_get st.vz major)
      else if mk = k_str then whnf st (string_to_ctor st (side_get st.vs major))
      else match induct with Some ind -> to_ctor_when_structure st ind major | None -> major in
    let ce = neu_const st major in
    if ce = 0 then None
    else begin
      let cn = side_get st.cname ce in
      match List.find_opt (fun rl -> Name.equal rl.r_ctor cn) rules with
      | None -> None
      | Some rule ->
        let mna = nargs st major in
        if rule.r_nfields > mna || List.compare_lengths ls ci.lparams <> 0 then None
        else begin
          let rce = const_entry st ci.name ls in
          let rhs = eval st 0 (sub_of st rce ci) rule.r_rhs in
          let rhs = apply_range st rhs args 0 (nparams + nmotives + nminors) in
          let margs = args_array st major in
          let rhs = apply_range st rhs margs (mna - rule.r_nfields) mna in
          Some (apply_range st rhs args (major_idx + 1) na)
        end
    end
  end

and to_ctor_when_k st induct major nparams =
  match type_of st major with
  | exception Decline _ -> major
  | ty ->
    let app_type = whnf st ty in
    let ce = neu_const st app_type in
    if ce = 0 || not (Name.equal (side_get st.cname ce) induct) then major
    else match Tc.ind_info st.tc induct with
      | Some { ctors = ctor :: _; _ } ->
        if nargs st app_type < nparams then major else begin
          let targs = args_array st app_type in
          let params = Array.to_list (Array.sub targs 0 nparams) in
          let c = mk_app st (g st.c (const_entry st ctor (side_get st.clev ce)) 0) params in
          match type_of st c with
          | exception Decline _ -> major
          | cty -> if conv st app_type cty then c else major
        end
      | _ -> major

and to_ctor_when_structure st induct major =
  if not (Tc.is_non_rec_structure st.tc induct) || ctor_of st major <> None then major
  else match type_of st major with
    | exception Decline _ -> major
    | ty ->
      let ty = whnf st ty in
      if is_const_name st ty induct then (if is_prop st ty then major else expand_eta_struct st ty major)
      else major

and expand_eta_struct st ty v =
  let ce = neu_const st ty in
  if ce = 0 then v else begin
    let n = side_get st.cname ce in
    match Tc.ind_info st.tc n with
    | Some { ctors = ctor :: _; _ } ->
      (match find st ctor with
       | Some { kind = Ctor { cnparams; nfields; _ }; _ } ->
         let targs = args_array st ty in
         let np = min cnparams (Array.length targs) in
         let params = Array.to_list (Array.sub targs 0 np) in
         let fields = List.init nfields (fun i -> of_value st (mk_proj st n i v)) in
         mk_app st (g st.c (const_entry st ctor (side_get st.clev ce)) 0) (params @ fields)
       | _ -> v)
    | _ -> v
  end

and nat_lit_ext st v =
  let k = kind st v in
  if k = k_nat then Some (side_get st.vz v)
  else if k = k_neu && nargs st v = 0 && is_const_name st v Tc.N.nat_zero
          && side_get st.clev (neu_const st v) = [] then Some Z.zero
  else None

and reduce_nat st v =
  if (not st.tc.Tc.bi.nat_ok) || vopen st v || kind st v <> k_neu then None else begin
    let ce = neu_const st v in
    if ce = 0 || side_get st.clev ce <> [] then None else begin
      let n = side_get st.cname ce in
      let na = nargs st v in
      if na = 1 && (n == Tc.N.nat_succ || Name.equal n Tc.N.nat_succ) then
        (match nat_lit_ext st (whnf st (force st (last_arg st v))) with
         | Some z -> Some (mk_nat st (Z.succ z))
         | None -> None)
      else if na = 2 then begin
        let sp = g st.v v f_b in
        let b = e_head st sp and a = e_head st (e_tail st sp) in
        let bin f =
          match nat_lit_ext st (whnf st (force st a)) with
          | None -> None
          | Some x ->
            match nat_lit_ext st (whnf st (force st b)) with
            | None -> None
            | Some y -> f x y in
        let size_ok r = if Z.numbits r / 8 > Tc.max_nat_bytes then fail "Nat numeral too large" else Some (mk_nat st r) in
        let nat r = Some (mk_nat st r) in
        let bool b = Some (const_val st (if b then Tc.N.bool_true else Tc.N.bool_false) []) in
        let module N = Tc.N in
        if n == N.nat_add then bin (fun a b -> size_ok (Z.add a b))
        else if n == N.nat_sub then bin (fun a b -> nat (if Z.leq a b then Z.zero else Z.sub a b))
        else if n == N.nat_mul then bin (fun a b -> size_ok (Z.mul a b))
        else if n == N.nat_pow then bin (fun a b ->
            if Z.gt b (Z.of_int 0xFFFFFFFF) then fail "Nat.pow exponent too large";
            let k = Z.to_int b in
            if Z.gt a Z.one && k <> 0 && (Z.numbits a / 8 + 1) > Tc.max_nat_bytes / k then fail "Nat.pow result too large";
            nat (Z.pow a k))
        else if n == N.nat_gcd then bin (fun a b -> nat (Z.gcd a b))
        else if n == N.nat_mod then bin (fun a b -> nat (if Z.equal b Z.zero then a else Z.rem a b))
        else if n == N.nat_div then bin (fun a b -> nat (if Z.equal b Z.zero then Z.zero else Z.div a b))
        else if n == N.nat_beq then bin (fun a b -> bool (Z.equal a b))
        else if n == N.nat_ble then bin (fun a b -> bool (Z.leq a b))
        else if n == N.nat_land then bin (fun a b -> nat (Z.logand a b))
        else if n == N.nat_lor then bin (fun a b -> nat (Z.logor a b))
        else if n == N.nat_xor then bin (fun a b -> nat (Z.logxor a b))
        else if n == N.nat_shl then bin (fun a b ->
            if Z.equal a Z.zero then nat Z.zero else begin
              if Z.gt b (Z.of_int 0xFFFFFFFF) then fail "Nat.shiftLeft amount too large";
              let k = Z.to_int b in
              if Z.numbits a / 8 + k / 8 + 1 > Tc.max_nat_bytes then fail "Nat.shiftLeft result too large";
              nat (Z.shift_left a k)
            end)
        else if n == N.nat_shr then bin (fun a b ->
            if Z.gt b (Z.of_int max_int) then nat Z.zero else nat (Z.shift_right a (Z.to_int b)))
        else None
      end else None
    end
  end

and whnf st v =
  if kind st v <> k_neu then v
  else begin
    let m = g st.v v f_wf in
    if m <> 0 then m
    else begin
      let rec loop t =
        tick st;
        let t1 = whnf_core st t in
        match reduce_nat st t1 with
        | Some r -> r
        | None ->
          match unfold st t1 with
          | Some t' -> loop t'
          | None -> t1 in
      enter st; cnt st 6;
      let r = loop v in
      leave st;
      p st.v v f_wf r; r
    end
  end

(* --------------------------------------------------------------- types *)
and type_of st v =
  let k = kind st v in
  if k = k_sort then mk_sort st (Level.succ (side_get st.vlev v))
  else if k = k_nat then nat_type st
  else if k = k_str then string_type st
  else if k = k_lam then decline "type of a lambda"
  else if k = k_pi then decline "type of a Pi"
  else begin
    let m = g st.v v f_ty in
    if m <> 0 then m
    else begin
      cnt st 9;
      let hd = g st.v v f_a in
      let hk = h_kind st hd in
      let h =
        if hk = h_const then const_type st (g st.h hd 1)
        else if hk = h_local then g st.h hd 1
        else proj_type st (side_get st.hname hd) (g st.h hd 1) (g st.h hd 2) in
      let rec go e = if e = 0 then h else begin
          let t = whnf st (go (e_tail st e)) in
          if kind st t = k_pi then inst_thunk st t (e_head st e) else decline "spine of a non-function"
        end in
      let t = go (g st.v v f_b) in
      p st.v v f_ty t; t
    end
  end

and proj_type st sname idx sv =
  let ty = whnf st (type_of st sv) in
  let ce = neu_const st ty in
  if ce = 0 || not (Name.equal (side_get st.cname ce) sname) then decline "projection" else
    match Tc.ind_info st.tc sname with
    | Some ({ ctors = [ctor]; _ } as iv) when nargs st ty = iv.nparams + iv.nindices ->
      let targs = args_array st ty in
      let r = ref (const_type st (const_entry st ctor (side_get st.clev ce))) in
      for i = 0 to iv.nparams - 1 do
        let t = whnf st !r in
        if kind st t = k_pi then r := inst_thunk st t targs.(i) else decline "projection"
      done;
      for j = 0 to idx - 1 do
        let t = whnf st !r in
        if kind st t = k_pi then r := inst st t (mk_proj st sname j sv) else decline "projection"
      done;
      let t = whnf st !r in
      if kind st t = k_pi then dom st t else decline "projection"
    | _ -> decline "projection"

and is_prop st ty =
  let t = whnf st ty in
  let k = kind st t in
  if k = k_pi then is_prop st (inst st t (fresh_local st (dom st t)))
  else if k = k_neu then begin
    let s = whnf st (type_of st t) in
    kind st s = k_sort && Level.normalizes_to_zero (side_get st.vlev s)
  end else false

(* ---------------------------------------------------------- conversion *)
and levels_eq la lb = List.compare_lengths la lb = 0 && List.for_all2 Level.is_equiv la lb

(* bounded syntactic equality; [true] means equal, [false] unknown *)
and same st a b fuel =
  a = b ||
  (!fuel > 0 && begin
      decr fuel;
      let k = kind st a in
      k = kind st b &&
      (if k = k_sort then (let x = side_get st.vlev a and y = side_get st.vlev b in x == y || Level.equal x y)
       else if k = k_nat then Z.equal (side_get st.vz a) (side_get st.vz b)
       else if k = k_str then String.equal (side_get st.vs a) (side_get st.vs b)
       else if k = k_neu then
         g st.v a f_c = g st.v b f_c && same_head st (g st.v a f_a) (g st.v b f_a) fuel
         && same_env st (g st.v a f_b) (g st.v b f_b) fuel
       else
         side_get st.vexp a == side_get st.vexp b && g st.v a f_b = g st.v b f_b
         && same_thunk st (g st.v a f_a) (g st.v b f_a) fuel
         && same_env st (g st.v a f_c) (g st.v b f_c) fuel)
    end)

and same_head st x y fuel =
  x = y ||
  (let k = h_kind st x in
   k = h_kind st y && k = h_proj && g st.h x 1 = g st.h y 1
   && Name.equal (side_get st.hname x) (side_get st.hname y) && same st (g st.h x 2) (g st.h y 2) fuel)

and same_thunk st x y fuel =
  x = y ||
  (let vx = g st.t x 2 and vy = g st.t y 2 in
   if vx = 0 && vy = 0 && side_get st.texp x == side_get st.texp y && g st.t x 0 = g st.t y 0
      && same_env st (g st.t x 1) (g st.t y 1) fuel then true
   else same st (force st x) (force st y) fuel)

and same_env st x y fuel =
  x = y ||
  (x <> 0 && y <> 0 && e_len st x = e_len st y &&
   same_thunk st (e_head st x) (e_head st y) fuel && same_env st (e_tail st x) (e_tail st y) fuel)

and pair_mem st tab a b =
  let a, b = if a < b then a, b else b, a in
  itab_find tab (mix3 a b 5) (fun x -> g st.pr x 0 = a && g st.pr x 1 = b) <> 0

and pair_add st tab a b =
  let a, b = if a < b then a, b else b, a in
  let h = mix3 a b 5 in
  if itab_find tab h (fun x -> g st.pr x 0 = a && g st.pr x 1 = b) = 0 then begin
    let x = ar_new st.pr in
    p st.pr x 0 a; p st.pr x 1 b; itab_add tab h x
  end

and quick st t s =
  if same st t s (ref 256) then (cnt st 5; 1) else begin
    let k = kind st t in
    if k <> kind st s then -1
    else if k = k_sort then (if Level.is_equiv (side_get st.vlev t) (side_get st.vlev s) then 1 else 0)
    else if k = k_nat then (if Z.equal (side_get st.vz t) (side_get st.vz s) then 1 else 0)
    else if k = k_str then (if String.equal (side_get st.vs t) (side_get st.vs s) then 1 else 0)
    else if k = k_lam || k = k_pi then begin
      let d1 = dom st t and d2 = dom st s in
      if d1 = d2 || conv st d1 d2 then begin
        let x = fresh_local st d2 in
        if conv st (inst st t x) (inst st s x) then 1 else 0
      end else 0
    end
    else if pair_mem st st.tab_succ t s then 1
    else -1
  end

and conv st t s =
  t = s ||
  begin
    cnt st 4; tick st; enter st;
    let r = quick st t s in
    let res = if r >= 0 then r = 1 else begin
        let r = conv_core st t s in
        if r && kind st t = k_neu && kind st s = k_neu then pair_add st st.tab_succ t s;
        r
      end in
    leave st; res
  end

and is_bool_true st v =
  kind st v = k_neu && nargs st v = 0 && is_const_name st v Tc.N.bool_true && side_get st.clev (neu_const st v) = []

and conv_core st t s =
  if ((not (vopen st t)) || st.eager) && is_bool_true st s && is_bool_true st (whnf st t) then true
  else begin
    let tn = whnf_core ~cheap:true st t and sn = whnf_core ~cheap:true st s in
    let r = if tn <> t || sn <> s then quick st tn sn else -1 in
    if r >= 0 then r = 1 else begin
      let r = proof_irrel st tn sn in
      if r >= 0 then r = 1 else begin
        match lazy_delta st tn sn with
        | `Eq -> true
        | `Neq -> false
        | `Unknown (tn, sn) ->
          let both_neu0 = kind st tn = k_neu && kind st sn = k_neu && nargs st tn = 0 && nargs st sn = 0 in
          let ht = if both_neu0 then g st.v tn f_a else 0 and hs = if both_neu0 then g st.v sn f_a else 0 in
          if both_neu0 && h_kind st ht = h_const && h_kind st hs = h_const
             && (let ca = g st.h ht 1 and cb = g st.h hs 1 in
                 Name.equal (side_get st.cname ca) (side_get st.cname cb)
                 && levels_eq (side_get st.clev ca) (side_get st.clev cb)) then true
          else if both_neu0 && h_kind st ht = h_local && ht = hs then true
          else begin
            let proj_ok =
              both_neu0 && h_kind st ht = h_proj && h_kind st hs = h_proj
              && g st.h ht 1 = g st.h hs 1 && Name.equal (side_get st.hname ht) (side_get st.hname hs)
              && lazy_delta_proj st (g st.h ht 2) (g st.h hs 2) (side_get st.hname ht) (g st.h ht 1) in
            proj_ok || begin
              let tnn = whnf_core st tn and snn = whnf_core st sn in
              if tnn <> tn || snn <> sn then conv st tnn snn
              else conv_app st tn sn || eta st tn sn || eta st sn tn
                   || eta_struct st tn sn || eta_struct st sn tn
                   || (match string_expand st tn sn with -1 -> string_expand st sn tn = 1 | r -> r = 1)
                   || unit_like st tn sn
            end
          end
      end
    end
  end

and proof_irrel st t s =
  let k = kind st t in
  if k = k_lam || k = k_pi || k = k_sort then -1
  else match type_of st t with
    | exception Decline _ -> -1
    | tt ->
      if not (is_prop st tt) then -1
      else match type_of st s with
        | exception Decline _ -> -1
        | ts -> if conv st tt ts then 1 else 0

and is_nat_zero st v = match nat_lit_ext st v with Some z -> Z.equal z Z.zero | None -> false

and nat_pred st v =
  let k = kind st v in
  if k = k_nat then (let z = side_get st.vz v in if Z.equal z Z.zero then None else Some (mk_nat st (Z.pred z)))
  else if k = k_neu && nargs st v = 1 && is_const_name st v Tc.N.nat_succ && side_get st.clev (neu_const st v) = []
  then Some (force st (last_arg st v))
  else None

and offset st t s =
  if not st.tc.Tc.bi.nat_ok then -1
  else if is_nat_zero st t && is_nat_zero st s then 1
  else match nat_pred st t, nat_pred st s with
    | Some a, Some b -> if conv_core_entry st a b then 1 else 0
    | _ -> -1

and conv_core_entry st a b = a = b || (let r = quick st a b in if r >= 0 then r = 1 else conv_core st a b)

and step st tn sn =
  let unfold_c v = match unfold st v with
    | Some v' -> whnf_core ~cheap:true st v'
    | None -> fail "unfold failed" in
  let proj_app v =
    if kind st v = k_neu && h_kind st (g st.v v f_a) = h_proj then
      (let v' = whnf_core st v in if v' <> v then Some v' else None)
    else None in
  let code, t', s' = match delta_info st tn, delta_info st sn with
    | None, None -> 3, tn, sn
    | Some _, None -> (match proj_app sn with Some s' -> 0, tn, s' | None -> 0, unfold_c tn, sn)
    | None, Some _ -> (match proj_app tn with Some t' -> 0, t', sn | None -> 0, tn, unfold_c sn)
    | Some d1, Some d2 ->
      let cmp = compare_hints (hints d1) (hints d2) in
      if cmp < 0 then 0, unfold_c tn, sn
      else if cmp > 0 then 0, tn, unfold_c sn
      else begin
        let shortcut =
          match hints d1 with
          | Regular _ when d1 == d2 && nargs st tn > 0 && nargs st sn > 0 ->
            if pair_mem st st.tab_fail tn sn then false
            else begin
              let la = side_get st.clev (neu_const st tn) and lb = side_get st.clev (neu_const st sn) in
              if levels_eq la lb && args_eq st tn sn then true
              else (pair_add st st.tab_fail tn sn; false)
            end
          | _ -> false in
        if shortcut then 1, tn, sn else 0, unfold_c tn, unfold_c sn
      end in
  if code <> 0 then (code, t', s')
  else match quick st t' s' with 1 -> (1, t', s') | 0 -> (2, t', s') | _ -> (0, t', s')

and args_eq st a b =
  nargs st a = nargs st b &&
  (let rec go x y =
     x = y || (x <> 0 && y <> 0 &&
               (let tx = e_head st x and ty = e_head st y in tx = ty || conv st (force st tx) (force st ty))
               && go (e_tail st x) (e_tail st y)) in
   go (g st.v a f_b) (g st.v b f_b))

and lazy_delta st tn sn =
  tick st;
  match offset st tn sn with
  | 1 -> `Eq
  | 0 -> `Neq
  | _ ->
    let try_nat =
      if ((not (vopen st tn)) && not (vopen st sn)) || st.eager then
        match reduce_nat st tn with
        | Some tv -> Some (if conv_core_entry st tv sn then `Eq else `Neq)
        | None -> match reduce_nat st sn with
          | Some sv -> Some (if conv_core_entry st tn sv then `Eq else `Neq)
          | None -> None
      else None in
    match try_nat with
    | Some r -> r
    | None ->
      match step st tn sn with
      | 0, t', s' -> lazy_delta st t' s'
      | 1, _, _ -> `Eq
      | 2, _, _ -> `Neq
      | _, t', s' -> `Unknown (t', s')

and lazy_delta_proj st e1 e2 sname idx =
  tick st;
  match step st e1 e2 with
  | 0, t', s' -> lazy_delta_proj st t' s' sname idx
  | 1, _, _ -> true
  | _, t, s ->
    (match proj_reduce st sname idx t with
     | Some a -> (match proj_reduce st sname idx s with
         | Some b -> conv_core_entry st a b
         | None -> conv_core_entry st t s)
     | None -> conv_core_entry st t s)

and heads_eq st x y =
  x = y ||
  (let k = h_kind st x in
   k = h_kind st y &&
   (if k = h_const then
      (let ca = g st.h x 1 and cb = g st.h y 1 in
       Name.equal (side_get st.cname ca) (side_get st.cname cb) && levels_eq (side_get st.clev ca) (side_get st.clev cb))
    else if k = h_proj then
      g st.h x 1 = g st.h y 1 && Name.equal (side_get st.hname x) (side_get st.hname y) && conv st (g st.h x 2) (g st.h y 2)
    else false))

and conv_app st t s =
  kind st t = k_neu && kind st s = k_neu && nargs st t > 0 && nargs st t = nargs st s
  && heads_eq st (g st.v t f_a) (g st.v s f_a) && args_eq st t s

and eta st t s =
  if kind st t <> k_lam || kind st s <> k_neu then false
  else match type_of st s with
    | exception Decline _ -> false
    | ty ->
      let ty = whnf st ty in
      if kind st ty <> k_pi then false
      else begin
        let sd = dom st ty in
        conv st (dom st t) sd &&
        (let x = fresh_local st sd in conv st (inst st t x) (apply st s (of_value st x)))
      end

and eta_struct st t s =
  match ctor_of st s with
  | Some (_, cv) when nargs st s = cv.cnparams + cv.nfields && Tc.is_non_rec_structure st.tc cv.induct ->
    (match type_of st t, type_of st s with
     | exception Decline _ -> false
     | tt, ts ->
       conv st tt ts &&
       (let args = args_array st s in
        let ok = ref true and i = ref cv.cnparams in
        while !ok && !i < Array.length args do
          if not (conv st (mk_proj st cv.induct (!i - cv.cnparams) t) (force st args.(!i))) then ok := false;
          incr i
        done; !ok))
  | _ -> false

and string_expand st t s =
  if kind st t = k_str && is_const_name st s Tc.N.string_of_list && st.tc.Tc.bi.str_ok then
    (if conv st (whnf st (string_to_ctor st (side_get st.vs t))) s then 1 else 0)
  else -1

and unit_like st t s =
  match type_of st t with
  | exception Decline _ -> false
  | tt ->
    let tt = whnf st tt in
    let ce = neu_const st tt in
    if ce = 0 then false else begin
      let n = side_get st.cname ce in
      Tc.is_non_rec_structure st.tc n &&
      (match Tc.ind_info st.tc n with
       | Some { ctors = [ctor]; _ } ->
         (match find st ctor with
          | Some { kind = Ctor { nfields = 0; _ }; _ } ->
            (match type_of st s with exception Decline _ -> false | ts -> conv st tt ts)
          | _ -> false)
       | _ -> false)
    end

(* -------------------------------------------------------------- typing *)
type cx = { env : int; tys : int list; cid : int }
let empty_cx = { env = 0; tys = []; cid = 0 }
let bind st cx th ty = st.ncx <- st.ncx + 1; { env = push st cx.env th; tys = ty :: cx.tys; cid = st.ncx }
let eval_cx st cx e = eval st cx.env 0 e
let check_level st l = Tc.check_level st.tc l

let infer_memo_find st e cid =
  let h = mix3 (Expr.hash e) cid 6 in
  let x = itab_find st.tab_inf h (fun x -> side_get st.infe x == e && g st.inf x 0 = cid) in
  if x = 0 then 0 else g st.inf x 1

let infer_memo_add st e cid t =
  let x = ar_new st.inf in
  p st.inf x 0 cid; p st.inf x 1 t; side_set st.infe x e;
  itab_add st.tab_inf (mix3 (Expr.hash e) cid 6) x

let rec infer st cx e =
  match e with
  | BVar { idx; _ } -> (try List.nth cx.tys idx with _ -> fail "type checker does not support loose bound variables")
  | FVar _ -> decline "free variable"
  | NatLit { n; _ } ->
    if not st.tc.Tc.bi.nat_ok then fail "Nat literal used, but Nat is not available";
    if Z.numbits n / 8 > Tc.max_nat_bytes then fail "Nat literal too large";
    nat_type st
  | StrLit _ ->
    if not st.tc.Tc.bi.str_ok then fail "String literal used, but String is not available";
    string_type st
  | Sort { l; _ } -> check_level st l; mk_sort st (Level.succ l)
  | Const { n; ls; _ } ->
    let ci = get st n in
    if List.compare_lengths ci.lparams ls <> 0 then
      fail "incorrect number of universe levels for '%s'" (Name.to_string n);
    if ci.unsafe && st.tc.Tc.safety <> Unsafe then
      fail "invalid declaration, it uses unsafe declaration '%s'" (Name.to_string n);
    (match ci.kind with
     | Defn { safety = Partial; _ } when st.tc.Tc.safety = Safe ->
       fail "invalid declaration, safe declaration must not contain partial declaration '%s'" (Name.to_string n)
     | _ -> ());
    List.iter (check_level st) ls;
    const_type st (const_entry st n ls)
  | _ when size e < Nbe.memo_size -> infer_node st cx e
  | _ ->
    let cid = if closed e then 0 else cx.cid in
    let t = infer_memo_find st e cid in
    if t <> 0 then t
    else (let t = infer_node st cx e in infer_memo_add st e cid t; t)

and infer_node st cx e =
  cnt st 10;
  match e with
  | App _ -> let f, args = get_app_args e in infer_app st cx f args
  | Lam _ -> decline "infer lambda"
  | Pi { ty; b; _ } ->
    let u = sort_of st cx ty in
    let d = eval_cx st cx ty in
    let x = fresh_local st d in
    let v = sort_of st (bind st cx (of_value st x) d) b in
    mk_sort st (Level.mk_imax u v)
  | Let { ty; v; b; _ } ->
    ignore (sort_of st cx ty);
    let tv = eval_cx st cx ty in
    check st cx v tv;
    infer st (bind st cx (mk_thunk st cx.env 0 v) tv) b
  | Proj { s; idx; e = se; _ } -> infer_proj st cx s idx se
  | _ -> infer st cx e

and infer_app st cx f args =
  let n = Array.length args in
  let rec peel cxb f i =
    match f with
    | Lam { ty; b; _ } when i < n ->
      ignore (sort_of st cxb ty);
      let d = eval_cx st cxb ty in
      check_arg st cx args.(i) d;
      peel (bind st cxb (mk_thunk st cx.env 0 args.(i)) d) b (i + 1)
    | _ -> (cxb, f, i) in
  let cx', f', i0 = peel cx f 0 in
  let tf = ref (infer st cx' f') in
  for i = i0 to n - 1 do
    let t = whnf st !tf in
    if kind st t = k_pi then begin
      check_arg st cx args.(i) (dom st t);
      tf := inst_thunk st t (mk_thunk st cx.env 0 args.(i))
    end else fail "function expected"
  done;
  !tf

and check_arg st cx a d =
  if is_app_of a Tc.N.eager_reduce && get_app_num_args a = 2 then begin
    let saved = st.eager in
    st.eager <- true;
    (match check st cx a d with () -> st.eager <- saved | exception ex -> st.eager <- saved; raise ex)
  end else check st cx a d

and sort_of st cx e =
  let t = whnf st (infer st cx e) in
  if kind st t = k_sort then side_get st.vlev t else fail "type expected"

and check st cx e expected =
  match e with
  | Lam { ty; b; _ } ->
    let ex = whnf st expected in
    if kind st ex = k_pi then begin
      ignore (sort_of st cx ty);
      let d = eval_cx st cx ty in
      if not (conv st d (dom st ex)) then fail "type mismatch (binder domain)";
      let x = fresh_local st d in
      check st (bind st cx (of_value st x) d) b (inst st ex x)
    end else decline "lambda against a non-Pi type"
  | Let { ty; v; b; _ } ->
    ignore (sort_of st cx ty);
    let tv = eval_cx st cx ty in
    check st cx v tv;
    check st (bind st cx (mk_thunk st cx.env 0 v) tv) b expected
  | _ ->
    let t = infer st cx e in
    if not (conv st t expected) then fail "type mismatch"

and infer_proj st cx sname idx se =
  let sty = whnf st (infer st cx se) in
  let bad () = fail "invalid projection" in
  let ce = neu_const st sty in
  if ce = 0 then bad ();
  let i_name = side_get st.cname ce and i_levels = side_get st.clev ce in
  if not (Name.equal i_name sname) then bad ();
  let iv = match Tc.ind_info st.tc i_name with Some iv -> iv | None -> bad () in
  let ctor = match iv.ctors with [ctor] -> ctor | _ -> bad () in
  if nargs st sty <> iv.nparams + iv.nindices then bad ();
  let ci = get st ctor in
  if List.compare_lengths ci.lparams i_levels <> 0 then bad ();
  let sv = eval_cx st cx se in
  let targs = args_array st sty in
  let r = ref (const_type st (const_entry st ctor i_levels)) in
  for i = 0 to iv.nparams - 1 do
    let t = whnf st !r in
    if kind st t = k_pi then r := inst_thunk st t targs.(i) else bad ()
  done;
  let is_prop_type = is_prop st sty in
  for j = 0 to idx - 1 do
    let t = whnf st !r in
    if kind st t = k_pi then begin
      if is_prop_type && not (is_prop st (dom st t)) then decline "projection past a non-propositional field";
      r := inst st t (mk_proj st i_name j sv)
    end else bad ()
  done;
  let t = whnf st !r in
  if kind st t = k_pi then begin
    let d = dom st t in
    if is_prop_type && not (is_prop st d) then bad ();
    d
  end else bad ()

(* --------------------------------------------------------------- entry *)
let check_decl (tc : Tc.ctx) (ci : cinfo) v =
  let st = Domain.DLS.get key in
  reset st tc;
  let fin () =
    if Nbe.stats_on then Array.iteri (fun i c -> ignore (Atomic.fetch_and_add Nbe.totals.(i) c)) st.counts in
  match
    let ty = eval st 0 0 ci.ty in
    check st empty_cx v ty
  with
  | () -> fin ()
  | exception e -> fin (); raise e
