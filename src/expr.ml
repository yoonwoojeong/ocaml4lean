(* Kernel expressions: locally nameless, de Bruijn indices for bound variables,
   hash-consed.  Binder names and binder infos are not stored: they have no
   influence on type checking, and dropping them makes alpha-equivalent terms
   physically equal.

   The cached info packs:  bit 0 = has free variables,  bit 1 = has universe
   parameters,  bit 2 = node lives in the global hash-cons tier,
   bits 3..10 = tree size (saturating at 255),
   bits 11.. = loose bound variable range (1 + max loose index). *)

type t =
  | BVar of { hi : int; idx : int }
  | FVar of { hi : int; id : int; ty : t; v : t option }
  | Sort of { hi : int; l : Level.t }
  | Const of { hi : int; n : Name.t; ls : Level.t list }
  | App of { hi : int; f : t; a : t }
  | Lam of { hi : int; ty : t; b : t }
  | Pi of { hi : int; ty : t; b : t }
  | Let of { hi : int; ty : t; v : t; b : t }
  | NatLit of { hi : int; n : Z.t }
  | StrLit of { hi : int; s : string }
  | Proj of { hi : int; s : Name.t; idx : int; e : t }

(* Every constructor is an inline record whose first field [hi] packs the
   31-bit structural hash (low bits) and the 32-bit cached info (high bits), so
   both are read without dispatching on the constructor, and each node needs
   one header word less (App/Lam/Pi: 4 words instead of 5). *)
let hash (e : t) : int = (Obj.obj (Obj.field (Obj.repr e) 0) : int) land 0x7FFFFFFF
let info (e : t) : int = (Obj.obj (Obj.field (Obj.repr e) 0) : int) lsr 31
(* The info word is 32 bits: lbr (bits 11..31) must stay below 2^21.  Loose
   bound variables are bounded by binder depth; a term needing more is refused
   (an internal error, never a verdict) rather than its range truncated, which
   could make an open term look closed. *)
exception Too_deep
let pack h i = if i lsr 32 <> 0 then raise Too_deep else (i lsl 31) lor (h land 0x7FFFFFFF)

let lbr e = info e lsr 11
let size e = (info e lsr 3) land 255
let has_fvar e = info e land 1 <> 0
let has_lparam e = info e land 2 <> 0
let is_global e = info e land 4 <> 0
let closed e = info e < 2048                   (* no loose bvars *)

module H = Hc.Make (struct
    type nonrec t = t
    let equal a b = match a, b with
      | BVar x, BVar y -> x.idx = y.idx
      | FVar x, FVar y -> x.id = y.id
      | Sort x, Sort y -> x.l == y.l
      | Const x, Const y ->
        x.n == y.n &&
        (let rec go a b = match a, b with
            | [], [] -> true
            | p :: a, q :: b -> p == q && go a b
            | _ -> false in go x.ls y.ls)
      | App x, App y -> x.f == y.f && x.a == y.a
      | Lam x, Lam y -> x.ty == y.ty && x.b == y.b
      | Pi x, Pi y -> x.ty == y.ty && x.b == y.b
      | Let x, Let y -> x.ty == y.ty && x.v == y.v && x.b == y.b
      | NatLit x, NatLit y -> Z.equal x.n y.n
      | StrLit x, StrLit y -> String.equal x.s y.s
      | Proj x, Proj y -> x.s == y.s && x.idx = y.idx && x.e == y.e
      | _ -> false
    let hash = hash
    let dummy = BVar { hi = 0; idx = 0 }
  end)

let mix = Hc.mix
let gbit () = if !Hc.frozen then 0 else 4
let mk_info ~fv ~lp ~lbr = (lbr lsl 11) lor 8 lor (if fv then 1 else 0) lor (if lp then 2 else 0) lor gbit ()
let union a b =
  let sz = min 255 (((a lsr 3) land 255) + ((b lsr 3) land 255) + 1) in
  (max (a lsr 11) (b lsr 11) lsl 11) lor (sz lsl 3) lor ((a lor b) land 3) lor gbit ()
(* info of a binder body: loose range decreases by one *)
let under i = let r = i lsr 11 in ((if r > 0 then r - 1 else 0) lsl 11) lor (i land 2043)
let g2 a b = info a land info b land 4 <> 0
let g3 a b c = info a land info b land info c land 4 <> 0

let small_bvars =
  Array.init 4096 (fun idx ->
    H.intern_g true (BVar { hi = pack (mix 101 idx) (mk_info ~fv:false ~lp:false ~lbr:(idx + 1)); idx }))

let[@inline] bvar idx =
  if idx < 4096 then Array.unsafe_get small_bvars idx
  else H.intern_g true (BVar { hi = pack (mix 101 idx) (mk_info ~fv:false ~lp:false ~lbr:(idx + 1)); idx })

let sort l =
  let h = mix 103 (Level.hash l) in
  if !Hc.frozen && !H.lookups then
    let g = H.global in
    let k = H.T.key h and hs = g.H.T.hs and vs = g.H.T.vs and mask = g.H.T.mask in
    let rec probe i =
      let x = H.T.hs_get hs i in
      if x = 0 then
        Sort { hi = pack h (mk_info ~fv:false ~lp:(Level.has_param l) ~lbr:0); l }
      else if x = k && (match Array.unsafe_get vs i with Sort y -> y.l == l | _ -> false) then
        Array.unsafe_get vs i
      else probe ((i + 1) land mask) in
    probe (k land mask)
  else
    H.intern_g true (Sort { hi = pack h (mk_info ~fv:false ~lp:(Level.has_param l) ~lbr:0); l })

let const n ls =
  let h = List.fold_left (fun h l -> mix h (Level.hash l)) (mix 107 (Name.hash n)) ls in
  if !Hc.frozen && !H.lookups then
    let g = H.global in
    let k = H.T.key h and hs = g.H.T.hs and vs = g.H.T.vs and mask = g.H.T.mask in
    let rec eq_ls a b = match a, b with [], [] -> true | p :: a, q :: b -> p == q && eq_ls a b | _ -> false in
    let rec probe i =
      let x = H.T.hs_get hs i in
      if x = 0 then
        Const { hi = pack h (mk_info ~fv:false ~lp:(List.exists Level.has_param ls) ~lbr:0); n; ls }
      else if x = k && (match Array.unsafe_get vs i with Const y -> y.n == n && eq_ls y.ls ls | _ -> false) then
        Array.unsafe_get vs i
      else probe ((i + 1) land mask) in
    probe (k land mask)
  else
    H.intern_g true (Const { hi = pack h (mk_info ~fv:false ~lp:(List.exists Level.has_param ls) ~lbr:0); n; ls })

(* After parsing, new nodes whose children are all in the (frozen) global tier
   are probed directly in [H.global] by hash and field identity BEFORE allocating
   the record, so global hits allocate 0 words and preserve the [is_global] bit. *)
let[@inline] app f a =
  let h = mix (mix 109 (hash f)) (hash a) in
  if !Hc.frozen then
    if g2 f a && !H.lookups then
      let g = H.global in
      let k = H.T.key h and hs = g.H.T.hs and vs = g.H.T.vs and mask = g.H.T.mask in
      let rec probe i =
        let x = H.T.hs_get hs i in
        if x = 0 then App { hi = pack h (union (info f) (info a)); f; a }
        else if x = k && (match Array.unsafe_get vs i with App y -> y.f == f && y.a == a | _ -> false) then
          Array.unsafe_get vs i
        else probe ((i + 1) land mask) in
      probe (k land mask)
    else App { hi = pack h (union (info f) (info a)); f; a }
  else H.intern_g true (App { hi = pack h (union (info f) (info a)); f; a })

let[@inline] lam ty b =
  let h = mix (mix 113 (hash ty)) (hash b) in
  if !Hc.frozen then
    if g2 ty b && !H.lookups then
      let g = H.global in
      let k = H.T.key h and hs = g.H.T.hs and vs = g.H.T.vs and mask = g.H.T.mask in
      let rec probe i =
        let x = H.T.hs_get hs i in
        if x = 0 then Lam { hi = pack h (union (info ty) (under (info b))); ty; b }
        else if x = k && (match Array.unsafe_get vs i with Lam y -> y.ty == ty && y.b == b | _ -> false) then
          Array.unsafe_get vs i
        else probe ((i + 1) land mask) in
      probe (k land mask)
    else Lam { hi = pack h (union (info ty) (under (info b))); ty; b }
  else H.intern_g true (Lam { hi = pack h (union (info ty) (under (info b))); ty; b })

let[@inline] pi ty b =
  let h = mix (mix 127 (hash ty)) (hash b) in
  if !Hc.frozen then
    if g2 ty b && !H.lookups then
      let g = H.global in
      let k = H.T.key h and hs = g.H.T.hs and vs = g.H.T.vs and mask = g.H.T.mask in
      let rec probe i =
        let x = H.T.hs_get hs i in
        if x = 0 then Pi { hi = pack h (union (info ty) (under (info b))); ty; b }
        else if x = k && (match Array.unsafe_get vs i with Pi y -> y.ty == ty && y.b == b | _ -> false) then
          Array.unsafe_get vs i
        else probe ((i + 1) land mask) in
      probe (k land mask)
    else Pi { hi = pack h (union (info ty) (under (info b))); ty; b }
  else H.intern_g true (Pi { hi = pack h (union (info ty) (under (info b))); ty; b })

let[@inline] let_ ty v b =
  H.intern_g (g3 ty v b)
    (Let { hi = pack (mix (mix (mix 131 (hash ty)) (hash v)) (hash b))
                   (union (union (info ty) (info v)) (under (info b))); ty; v; b })
let natlit n = H.intern_g true (NatLit { hi = pack (mix 137 (Z.hash n)) (8 lor gbit ()); n })
let strlit s = H.intern_g true (StrLit { hi = pack (mix 139 (Hashtbl.hash s)) (8 lor gbit ()); s })
let[@inline] proj s idx e =
  H.intern_g (is_global e) (Proj { hi = pack (mix (mix (mix 149 (Name.hash s)) idx) (hash e)) ((info e land (lnot 4)) lor gbit ()); s; idx; e })


(* Free variables are never shared between domains: per-domain counter. *)
let fv_counter = Domain.DLS.new_key (fun () -> ref 0)
let mk_fvar ?v ty =
  let c = Domain.DLS.get fv_counter in
  incr c;
  let id = !c in
  FVar { hi = pack (mix 151 id) 9; id; ty; v }

let fvar_ty = function FVar { ty; _ } -> ty | _ -> invalid_arg "fvar_ty"

(* ---------- structural equality ----------
   Free-variable-free nodes are hash-consed, so for them physical equality is
   structural equality.  Two terms can only be equal if both or neither contain
   free variables; only then is a structural walk needed.  The walk is
   memoised once it gets large, so shared sub-DAGs are not unfolded. *)
module PairTbl = Hashtbl.Make (struct
    type nonrec t = t * t
    let equal (a, b) (c, d) = a == c && b == d
    let hash (a, b) = mix (hash a) (hash b)
  end)

let equal a b =
  a == b ||
  (hash a = hash b && not (is_global a && is_global b) &&
   (let budget = ref 4096 in
    let memo = ref None in
    let rec eq a b =
      a == b ||
      (hash a = hash b && not (is_global a && is_global b) &&
       begin
         decr budget;
         if !budget < 0 then begin
           let m = match !memo with Some m -> m | None -> let m = PairTbl.create 256 in memo := Some m; m in
           if PairTbl.mem m (a, b) then true
           else begin
             let r = shallow a b in
             if r then PairTbl.replace m (a, b) ();
             r
           end
         end else shallow a b
       end)
    and shallow a b = match a, b with
      | BVar x, BVar y -> x.idx = y.idx
      | FVar x, FVar y -> x.id = y.id
      | Sort x, Sort y -> Level.equal x.l y.l
      | Const x, Const y ->
        Name.equal x.n y.n && List.compare_lengths x.ls y.ls = 0 && List.for_all2 Level.equal x.ls y.ls
      | App x, App y -> eq x.f y.f && eq x.a y.a
      | Lam x, Lam y -> eq x.ty y.ty && eq x.b y.b
      | Pi x, Pi y -> eq x.ty y.ty && eq x.b y.b
      | Let x, Let y -> eq x.ty y.ty && eq x.v y.v && eq x.b y.b
      | NatLit x, NatLit y -> Z.equal x.n y.n
      | StrLit x, StrLit y -> String.equal x.s y.s
      | Proj x, Proj y -> Name.equal x.s y.s && x.idx = y.idx && eq x.e y.e
      | _ -> false in
    shallow a b))

(* Open-addressing map keyed by expressions (structural equality), storing
   hashes inline so that probing compares ints before calling [equal]. *)
type expr = t
module Emap = struct
  type 'a t = { mutable hs : int array; mutable ks : expr array; mutable vs : 'a array;
                mutable n : int; mutable mask : int; mutable used : int array; dk : expr; dv : 'a }
  let dummy_key = BVar { hi = 0; idx = 0 }
  let create dv cap =
    let cap = let c = ref 16 in while !c < 2 * cap do c := 2 * !c done; !c in
    { hs = Array.make cap 0; ks = Array.make cap dummy_key; vs = Array.make cap dv; n = 0; mask = cap - 1;
      used = Array.make (cap / 2) 0; dk = dummy_key; dv }
  let clear t =
    if t.n > 0 then begin
      if t.mask + 1 > (1 lsl 15) then begin
        let cap = 256 in
        t.hs <- Array.make cap 0; t.ks <- Array.make cap t.dk; t.vs <- Array.make cap t.dv;
        t.mask <- cap - 1; t.used <- Array.make (cap / 2) 0
      end else begin
        for k = 0 to t.n - 1 do
          let i = Array.unsafe_get t.used k in
          Array.unsafe_set t.hs i 0;
          Array.unsafe_set t.ks i t.dk;
          Array.unsafe_set t.vs i t.dv
        done
      end;
      t.n <- 0
    end
  let[@inline] key h = (h lor 1) land max_int
  let find t (k : expr) =
    let h = key (hash k) in
    let hs = t.hs and mask = t.mask in
    let rec go i =
      let x = Array.unsafe_get hs i in
      if x = 0 then raise Not_found
      else if x = h && equal (Array.unsafe_get t.ks i) k then Array.unsafe_get t.vs i
      else go ((i + 1) land mask) in
    go (h land mask)
  let rec slot hs mask i = if Array.unsafe_get hs i = 0 then i else slot hs mask ((i + 1) land mask)
  let grow t =
    let cap = 2 * (t.mask + 1) in
    let mask = cap - 1 in
    let hs = Array.make cap 0 and ks = Array.make cap t.dk and vs = Array.make cap t.dv in
    let used = Array.make (cap / 2) 0 in
    for k = 0 to t.n - 1 do
      let i = Array.unsafe_get t.used k in
      let h = Array.unsafe_get t.hs i in
      let j = slot hs mask (h land mask) in
      Array.unsafe_set hs j h;
      Array.unsafe_set ks j (Array.unsafe_get t.ks i);
      Array.unsafe_set vs j (Array.unsafe_get t.vs i);
      Array.unsafe_set used k j
    done;
    t.hs <- hs; t.ks <- ks; t.vs <- vs; t.mask <- mask; t.used <- used
  (* add without checking for an existing binding (callers add after a miss) *)
  let add t k v =
    if 2 * (t.n + 1) > t.mask + 1 then grow t;
    let h = key (hash k) in
    let j = slot t.hs t.mask (h land t.mask) in
    Array.unsafe_set t.hs j h;
    Array.unsafe_set t.ks j k;
    Array.unsafe_set t.vs j v;
    Array.unsafe_set t.used t.n j;
    t.n <- t.n + 1
end

(* Open-addressing set of unordered expression pairs (structural equality),
   used for the definitional-equality success/failure caches. *)
module Pset = struct
  type t = { mutable hs : int array; mutable as_ : expr array; mutable bs : expr array;
             mutable n : int; mutable mask : int; mutable used : int array }
  let create cap =
    let cap = let c = ref 16 in while !c < 2 * cap do c := 2 * !c done; !c in
    { hs = Array.make cap 0; as_ = Array.make cap Emap.dummy_key; bs = Array.make cap Emap.dummy_key;
      n = 0; mask = cap - 1; used = Array.make (cap / 2) 0 }
  let clear t =
    if t.n > 0 then begin
      if t.mask + 1 > (1 lsl 15) then begin
        let cap = 64 in
        t.hs <- Array.make cap 0; t.as_ <- Array.make cap Emap.dummy_key; t.bs <- Array.make cap Emap.dummy_key;
        t.mask <- cap - 1; t.used <- Array.make (cap / 2) 0
      end else begin
        for k = 0 to t.n - 1 do
          let i = Array.unsafe_get t.used k in
          Array.unsafe_set t.hs i 0;
          Array.unsafe_set t.as_ i Emap.dummy_key;
          Array.unsafe_set t.bs i Emap.dummy_key
        done
      end;
      t.n <- 0
    end
  (* order the pair by hash so that (a, b) and (b, a) are the same key *)
  let[@inline] key a b = let ha = hash a and hb = hash b in
    if ha <= hb then ((mix ha hb) lor 1) land max_int else ((mix hb ha) lor 1) land max_int
  let mem t a b =
    let h = key a b in
    let mask = t.mask in
    let rec go i =
      let x = Array.unsafe_get t.hs i in
      if x = 0 then false
      else if x = h &&
              (let p = Array.unsafe_get t.as_ i and q = Array.unsafe_get t.bs i in
               (equal p a && equal q b) || (equal p b && equal q a)) then true
      else go ((i + 1) land mask) in
    go (h land mask)
  let rec slot hs mask i = if Array.unsafe_get hs i = 0 then i else slot hs mask ((i + 1) land mask)
  let grow t =
    let cap = 2 * (t.mask + 1) in
    let mask = cap - 1 in
    let hs = Array.make cap 0 and as_ = Array.make cap Emap.dummy_key and bs = Array.make cap Emap.dummy_key in
    let used = Array.make (cap / 2) 0 in
    for k = 0 to t.n - 1 do
      let i = Array.unsafe_get t.used k in
      let h = Array.unsafe_get t.hs i in
      let j = slot hs mask (h land mask) in
      Array.unsafe_set hs j h;
      Array.unsafe_set as_ j (Array.unsafe_get t.as_ i);
      Array.unsafe_set bs j (Array.unsafe_get t.bs i);
      Array.unsafe_set used k j
    done;
    t.hs <- hs; t.as_ <- as_; t.bs <- bs; t.mask <- mask; t.used <- used
  let add t a b =
    if not (mem t a b) then begin
      if 2 * (t.n + 1) > t.mask + 1 then grow t;
      let h = key a b in
      let j = slot t.hs t.mask (h land t.mask) in
      Array.unsafe_set t.hs j h;
      Array.unsafe_set t.as_ j a;
      Array.unsafe_set t.bs j b;
      Array.unsafe_set t.used t.n j;
      t.n <- t.n + 1
    end
end

(* ---------- application spines ---------- *)
let rec get_app_fn = function App { f; _ } -> get_app_fn f | e -> e
let get_app_num_args e =
  let rec go acc = function App { f; _ } -> go (acc + 1) f | _ -> acc in
  go 0 e

(* returns head and args in application order *)
let get_app_args e =
  let n = get_app_num_args e in
  let args = Array.make n e in
  let rec go e k = match e with
    | App { f; a; _ } -> args.(k) <- a; go f (k - 1)
    | _ -> e in
  let f = go e (n - 1) in
  (f, args)

let mk_app_arr f args = Array.fold_left app f args
let mk_app_sub f args lo hi = (* args.(lo) .. args.(hi-1) *)
  let r = ref f in for k = lo to hi - 1 do r := app !r args.(k) done; !r
let mk_app_list f args = List.fold_left app f args

let is_app_of e n = match get_app_fn e with Const { n = m; _ } -> m == n || Name.equal m n | _ -> false

(* ---------- caches for traversals over DAGs ---------- *)
module Tbl = Hashtbl.Make (struct type nonrec t = t let equal = equal let hash = hash end)
module PhysTbl = Hashtbl.Make (struct type nonrec t = t let equal = ( == ) let hash = hash end)
module Tbl2 = Hashtbl.Make (struct
    type nonrec t = t * int
    let equal (a, i) (b, j) = a == b && i = j
    let hash (a, i) = mix (hash a) i
  end)

(* Exact memo tables keyed by (node identity, binder offset), one per domain
   and traversal kind, reused across calls: entries live in flat arrays (no
   per-entry allocation, hence no promotion of cache cells by the GC), and a
   list of used slots makes clearing proportional to the previous use. *)
module Memo = struct
  type m = { mutable hs : int array; mutable ks : t array; mutable offs : int array; mutable vs : t array;
             mutable n : int; mutable mask : int; mutable used : int array }
  let dummy = BVar { hi = 0; idx = 0 }
  let init_cap = 1024
  let create () = { hs = Array.make init_cap 0; ks = Array.make init_cap dummy; offs = Array.make init_cap 0;
                    vs = Array.make init_cap dummy; n = 0; mask = init_cap - 1; used = Array.make (init_cap / 2) 0 }
  let clear m =
    if m.n > 0 then begin
      if m.mask + 1 > (1 lsl 16) then begin
        m.hs <- Array.make init_cap 0; m.ks <- Array.make init_cap dummy; m.offs <- Array.make init_cap 0;
        m.vs <- Array.make init_cap dummy; m.mask <- init_cap - 1; m.used <- Array.make (init_cap / 2) 0
      end else
        for k = 0 to m.n - 1 do
          let i = Array.unsafe_get m.used k in
          Array.unsafe_set m.hs i 0; Array.unsafe_set m.ks i dummy; Array.unsafe_set m.vs i dummy
        done;
      m.n <- 0
    end
  let key e off = ((mix (hash e) off) lor 1) land max_int
  let find m e off =
    let h = key e off in
    let mask = m.mask in
    let rec go i =
      let x = Array.unsafe_get m.hs i in
      if x = 0 then raise Not_found
      else if x = h && Array.unsafe_get m.ks i == e && Array.unsafe_get m.offs i = off then Array.unsafe_get m.vs i
      else go ((i + 1) land mask) in
    go (h land mask)
  let rec slot hs mask h i = if Array.unsafe_get hs i = 0 then i else slot hs mask h ((i + 1) land mask)
  let grow m =
    let cap = 2 * (m.mask + 1) in
    let mask = cap - 1 in
    let hs = Array.make cap 0 and ks = Array.make cap dummy and offs = Array.make cap 0 and vs = Array.make cap dummy in
    let used = Array.make (cap / 2) 0 in
    for k = 0 to m.n - 1 do
      let i = m.used.(k) in
      let h = m.hs.(i) in
      let j = slot hs mask h (h land mask) in
      hs.(j) <- h; ks.(j) <- m.ks.(i); offs.(j) <- m.offs.(i); vs.(j) <- m.vs.(i); used.(k) <- j
    done;
    m.hs <- hs; m.ks <- ks; m.offs <- offs; m.vs <- vs; m.mask <- mask; m.used <- used
  let add m e off v =
    if 2 * (m.n + 1) > m.mask + 1 then grow m;
    let h = key e off in
    let j = slot m.hs m.mask h (h land m.mask) in
    Array.unsafe_set m.hs j h; Array.unsafe_set m.ks j e; Array.unsafe_set m.offs j off; Array.unsafe_set m.vs j v;
    Array.unsafe_set m.used m.n j;
    m.n <- m.n + 1
  let key_dls = Domain.DLS.new_key (fun () -> Array.init 6 (fun _ -> create ()))
  (* traversal kinds: 0 lift, 1 lower, 2 instantiate, 3 abstract, 4 lparams *)
  let get k = let m = (Domain.DLS.get key_dls).(k) in clear m; m
end

(* Only subterms of at least this (tree) size are memoised: smaller ones are
   cheaper to rebuild than to look up, and exponential blow-up through DAG
   sharing can only come from large shared subterms. *)
let memo_min = (match Sys.getenv_opt "O4L_MEMO_MIN" with Some v -> int_of_string v | None -> 0)

(* lift loose bvars >= s by d *)
let lift_loose e s d =
  if d = 0 || lbr e <= s then e else begin
    let cache = Memo.get 0 in
    let rec go e off =
      if lbr e <= s + off then e else
        match e with
        | BVar { idx; _ } -> bvar (idx + d)
        | _ ->
          match (if size e < memo_min then raise Not_found else Memo.find cache e off) with
          | r -> r
          | exception Not_found ->
            let r = match e with
              | App { f; a; _ } ->
                let f' = go f off and a' = go a off in
                if f' == f && a' == a then e else app f' a'
              | Lam { ty; b; _ } ->
                let ty' = go ty off and b' = go b (off + 1) in
                if ty' == ty && b' == b then e else lam ty' b'
              | Pi { ty; b; _ } ->
                let ty' = go ty off and b' = go b (off + 1) in
                if ty' == ty && b' == b then e else pi ty' b'
              | Let { ty; v; b; _ } ->
                let ty' = go ty off and v' = go v off and b' = go b (off + 1) in
                if ty' == ty && v' == v && b' == b then e else let_ ty' v' b'
              | Proj { s; idx; e = st; _ } ->
                let st' = go st off in
                if st' == st then e else proj s idx st'
              | _ -> e in
            if size e >= memo_min then Memo.add cache e off r; r in
    go e 0
  end

(* lower loose bvars >= s by d (caller guarantees no bvar in [s-d, s) occurs) *)
let lower_loose e s d =
  if d = 0 || lbr e <= s then e else begin
    let cache = Memo.get 1 in
    let rec go e off =
      if lbr e <= s + off then e else
        match e with
        | BVar { idx; _ } -> bvar (idx - d)
        | _ ->
          match (if size e < memo_min then raise Not_found else Memo.find cache e off) with
          | r -> r
          | exception Not_found ->
            let r = match e with
              | App { f; a; _ } ->
                let f' = go f off and a' = go a off in
                if f' == f && a' == a then e else app f' a'
              | Lam { ty; b; _ } ->
                let ty' = go ty off and b' = go b (off + 1) in
                if ty' == ty && b' == b then e else lam ty' b'
              | Pi { ty; b; _ } ->
                let ty' = go ty off and b' = go b (off + 1) in
                if ty' == ty && b' == b then e else pi ty' b'
              | Let { ty; v; b; _ } ->
                let ty' = go ty off and v' = go v off and b' = go b (off + 1) in
                if ty' == ty && v' == v && b' == b then e else let_ ty' v' b'
              | Proj { s; idx; e = st; _ } ->
                let st' = go st off in
                if st' == st then e else proj s idx st'
              | _ -> e in
            if size e >= memo_min then Memo.add cache e off r; r in
    go e 0
  end

(* instantiate e with subst: loose bvar (off + k) for k < n becomes subst k
   (lifted by off), bvar (off + k) for k >= n becomes bvar (off + k - n).
   [subst k] = arr.(base - k) if [rev] else arr.(base + k). *)
let instantiate_core e n (arr : t array) base rev =
  if closed e || n = 0 then e else begin
    let cache = Memo.get 2 in
    let get k = if rev then Array.unsafe_get arr (base - k) else Array.unsafe_get arr (base + k) in
    let rec go e off =
      if lbr e <= off then e else
        match e with
        | BVar { idx; _ } ->
          let k = idx - off in
          if k < n then lift_loose (get k) 0 off else bvar (idx - n)
        | _ ->
          match (if size e < memo_min then raise Not_found else Memo.find cache e off) with
          | r -> r
          | exception Not_found ->
            let r = match e with
              | App { f; a; _ } ->
                let f' = go f off and a' = go a off in
                if f' == f && a' == a then e else app f' a'
              | Lam { ty; b; _ } ->
                let ty' = go ty off and b' = go b (off + 1) in
                if ty' == ty && b' == b then e else lam ty' b'
              | Pi { ty; b; _ } ->
                let ty' = go ty off and b' = go b (off + 1) in
                if ty' == ty && b' == b then e else pi ty' b'
              | Let { ty; v; b; _ } ->
                let ty' = go ty off and v' = go v off and b' = go b (off + 1) in
                if ty' == ty && v' == v && b' == b then e else let_ ty' v' b'
              | Proj { s; idx; e = st; _ } ->
                let st' = go st off in
                if st' == st then e else proj s idx st'
              | _ -> e in
            if size e >= memo_min then Memo.add cache e off r; r in
    go e 0
  end

let instantiate_gen e n (get : int -> t) = instantiate_core e n (Array.init n get) 0 false

(* bvar 0 := v *)
let instantiate1 e v =
  if closed e then e else begin
    let cache = Memo.get 2 in
    let rec go e off =
      if lbr e <= off then e else
        match e with
        | BVar { idx; _ } -> if idx = off then lift_loose v 0 off else bvar (idx - 1)
        | _ ->
          match (if size e < memo_min then raise Not_found else Memo.find cache e off) with
          | r -> r
          | exception Not_found ->
            let r = match e with
              | App { f; a; _ } ->
                let f' = go f off and a' = go a off in
                if f' == f && a' == a then e else app f' a'
              | Lam { ty; b; _ } ->
                let ty' = go ty off and b' = go b (off + 1) in
                if ty' == ty && b' == b then e else lam ty' b'
              | Pi { ty; b; _ } ->
                let ty' = go ty off and b' = go b (off + 1) in
                if ty' == ty && b' == b then e else pi ty' b'
              | Let { ty; v; b; _ } ->
                let ty' = go ty off and v' = go v off and b' = go b (off + 1) in
                if ty' == ty && v' == v && b' == b then e else let_ ty' v' b'
              | Proj { s; idx; e = st; _ } ->
                let st' = go st off in
                if st' == st then e else proj s idx st'
              | _ -> e in
            if size e >= memo_min then Memo.add cache e off r; r in
    go e 0
  end

(* Lean's instantiate(e, n, s): bvar k := s.(k) *)
let instantiate e (s : t array) = instantiate_core e (Array.length s) s 0 false
(* Lean's instantiate_rev(e, n, s): bvar k := s.(n-1-k) *)
let instantiate_rev e (s : t array) =
  let n = Array.length s in instantiate_core e n s (n - 1) true
let instantiate_rev_sub e (s : t array) n = instantiate_core e n s (n - 1) true
(* bvar k := args.(hi - 1 - k) for k < hi - lo: the arguments args.(lo..hi-1) as a
   reversed substitution, as used for beta reduction of [f args] *)
let instantiate_args e (args : t array) lo hi = instantiate_core e (hi - lo) args (hi - 1) true

(* abstract fvars xs.(0..n-1): fvar xs.(j) becomes bvar (off + n - 1 - j) *)
let abstract e (xs : t array) n =
  if not (has_fvar e) || n = 0 then e else begin
    let cache = Memo.get 3 in
    let id0 = match Array.unsafe_get xs 0 with FVar x -> x.id | _ -> -1 in
    let id_last = match Array.unsafe_get xs (n - 1) with FVar x -> x.id | _ -> -2 in
    (* When [xs] was created by a single binder loop without inner fvar creation,
       the IDs are strictly contiguous: xs.(j).id = id0 + j. *)
    let is_contig =
      id0 >= 0 && id_last - id0 = n - 1 &&
      (let ok = ref true in
       for j = 0 to n - 1 do
         match Array.unsafe_get xs j with
         | FVar x when x.id = id0 + j -> ()
         | _ -> ok := false
       done; !ok) in
    let[@inline] find_idx id =
      if is_contig then
        let j = id - id0 in
        if j >= 0 && j < n then j else -1
      else
        let rec find j = if j < 0 then -1 else
            (match Array.unsafe_get xs j with FVar x when x.id = id -> j | _ -> find (j - 1)) in
        find (n - 1) in
    let rec go e off =
      if not (has_fvar e) then e else
        match e with
        | FVar { id; _ } ->
          let j = find_idx id in if j < 0 then e else bvar (off + n - 1 - j)
        | _ ->
          match (if size e < memo_min then raise Not_found else Memo.find cache e off) with
          | r -> r
          | exception Not_found ->
            let r = match e with
              | App { f; a; _ } ->
                let f' = go f off and a' = go a off in
                if f' == f && a' == a then e else app f' a'
              | Lam { ty; b; _ } ->
                let ty' = go ty off and b' = go b (off + 1) in
                if ty' == ty && b' == b then e else lam ty' b'
              | Pi { ty; b; _ } ->
                let ty' = go ty off and b' = go b (off + 1) in
                if ty' == ty && b' == b then e else pi ty' b'
              | Let { ty; v; b; _ } ->
                let ty' = go ty off and v' = go v off and b' = go b (off + 1) in
                if ty' == ty && v' == v && b' == b then e else let_ ty' v' b'
              | Proj { s; idx; e = st; _ } ->
                let st' = go st off in
                if st' == st then e else proj s idx st'
              | _ -> e in
            if size e >= memo_min then Memo.add cache e off r; r in
    go e 0
  end


let has_loose_bvar0 e =
  (* does bvar 0 occur loosely? *)
  if closed e then false else begin
    let seen = Memo.get 5 in
    let rec go e off =
      if lbr e <= off then false
      else match e with
        | BVar { idx; _ } -> idx = off
        | _ ->
          match Memo.find seen e off with
          | _ -> false
          | exception Not_found ->
            Memo.add seen e off e;
            match e with
            | App { f; a; _ } -> go f off || go a off
            | Lam { ty; b; _ } | Pi { ty; b; _ } -> go ty off || go b (off + 1)
            | Let { ty; v; b; _ } -> go ty off || go v off || go b (off + 1)
            | Proj { e; _ } -> go e off
            | _ -> false in
    go e 0
  end

(* Lean's local_ctx::mk_binding.  [is_lam] chooses lambda/pi; let-fvars become
   lets (dead ones removed when [remove_dead_let]). *)
let mk_binding is_lam (xs : t array) n b remove_dead_let =
  let r = ref (abstract b xs n) in
  for i = n - 1 downto 0 do
    match xs.(i) with
    | FVar { ty; v = Some v; _ } ->
      if (not remove_dead_let) || has_loose_bvar0 !r then
        r := let_ (abstract ty xs i) (abstract v xs i) !r
      else r := lower_loose !r 1 1
    | FVar { ty; _ } ->
      let ty = abstract ty xs i in
      r := if is_lam then lam ty !r else pi ty !r
    | _ -> assert false
  done;
  !r

let mk_pi xs b = mk_binding false xs (Array.length xs) b false
let mk_lambda xs b = mk_binding true xs (Array.length xs) b false
let mk_pi_l xs b = mk_pi (Array.of_list xs) b
let mk_lambda_l xs b = mk_lambda (Array.of_list xs) b

(* ---------- universe parameter instantiation ---------- *)
let instantiate_lparams e (ps : Name.t list) (ls : Level.t list) =
  if (match ps with [] -> true | _ -> false) || not (has_lparam e) then e else begin
    let cache = Memo.get 4 in
    let lv l = Level.instantiate ps ls l in
    let rec go e =
      if not (has_lparam e) then e else
        match (if size e < memo_min then raise Not_found else Memo.find cache e 0) with
        | r -> r
        | exception Not_found ->
          let r = match e with
            | Sort { l; _ } ->
              let l' = lv l in if l' == l then e else sort l'
            | Const { n; ls; _ } -> const n (List.map lv ls)
            | App { f; a; _ } ->
              let f' = go f and a' = go a in
              if f' == f && a' == a then e else app f' a'
            | Lam { ty; b; _ } ->
              let ty' = go ty and b' = go b in
              if ty' == ty && b' == b then e else lam ty' b'
            | Pi { ty; b; _ } ->
              let ty' = go ty and b' = go b in
              if ty' == ty && b' == b then e else pi ty' b'
            | Let { ty; v; b; _ } ->
              let ty' = go ty and v' = go v and b' = go b in
              if ty' == ty && v' == v && b' == b then e else let_ ty' v' b'
            | Proj { s; idx; e = st; _ } ->
              let st' = go st in
              if st' == st then e else proj s idx st'
            | _ -> e in
          if size e >= memo_min then Memo.add cache e 0 r; r in
    go e
  end


(* generic search: does some subterm satisfy p ? (p is applied to every node) *)
let exists p e =
  let seen = PhysTbl.create 64 in
  let rec go e =
    if PhysTbl.mem seen e then false else begin
      PhysTbl.add seen e ();
      p e || (match e with
          | App { f; a; _ } -> go f || go a
          | Lam { ty; b; _ } | Pi { ty; b; _ } -> go ty || go b
          | Let { ty; v; b; _ } -> go ty || go v || go b
          | Proj { e; _ } -> go e
          | FVar _ | BVar _ | Sort _ | Const _ | NatLit _ | StrLit _ -> false)
    end in
  go e

(* generic replace (no binder offset tracking needed by callers here) *)
let replace (f : t -> t option) e =
  let cache = PhysTbl.create 64 in
  let rec go e =
    match PhysTbl.find cache e with
    | r -> r
    | exception Not_found ->
      (* The callback may have side effects (nested-inductive elimination
         creates auxiliary types as it meets occurrences), so children are
         visited in Lean's order -- function before argument, domain before
         body -- made explicit with [let], since OCaml evaluates constructor
         arguments right to left. *)
      let r = match f e with
        | Some r -> r
        | None -> match e with
          | App { f; a; _ } -> let f = go f in let a = go a in app f a
          | Lam { ty; b; _ } -> let ty = go ty in let b = go b in lam ty b
          | Pi { ty; b; _ } -> let ty = go ty in let b = go b in pi ty b
          | Let { ty; v; b; _ } -> let ty = go ty in let v = go v in let b = go b in let_ ty v b
          | Proj { s; idx; e; _ } -> proj s idx (go e)
          | _ -> e in
      PhysTbl.add cache e r; r in
  go e

(* ---------- printing (diagnostics only) ---------- *)
let to_string ?(max = 2000) e =
  let b = Buffer.create 256 in
  let rec go e =
    if Buffer.length b > max then () else
      match e with
      | BVar { idx; _ } -> Buffer.add_string b ("#" ^ string_of_int idx)
      | FVar { id; _ } -> Buffer.add_string b ("_x" ^ string_of_int id)
      | Sort { l; _ } -> Buffer.add_string b ("Sort " ^ Level.to_string l)
      | Const { n; ls; _ } ->
        Buffer.add_string b (Name.to_string n);
        if ls <> [] then Buffer.add_string b (".{" ^ String.concat ", " (List.map Level.to_string ls) ^ "}")
      | App _ ->
        let f, args = get_app_args e in
        Buffer.add_char b '('; go f;
        Array.iter (fun a -> Buffer.add_char b ' '; go a) args; Buffer.add_char b ')'
      | Lam { ty; b = bd; _ } -> Buffer.add_string b "(fun _ : "; go ty; Buffer.add_string b " => "; go bd; Buffer.add_char b ')'
      | Pi { ty; b = bd; _ } -> Buffer.add_string b "((_ : "; go ty; Buffer.add_string b ") -> "; go bd; Buffer.add_char b ')'
      | Let { ty; v; b = bd; _ } -> Buffer.add_string b "(let _ : "; go ty; Buffer.add_string b " := "; go v; Buffer.add_string b "; "; go bd; Buffer.add_char b ')'
      | NatLit { n; _ } -> Buffer.add_string b (Z.to_string n)
      | StrLit { s; _ } -> Buffer.add_string b (Printf.sprintf "%S" s)
      | Proj { s; idx; e; _ } -> go e; Buffer.add_string b ("." ^ Name.to_string s ^ "." ^ string_of_int (idx + 1)) in
  go e;
  if Buffer.length b > max then Buffer.sub b 0 max ^ "..." else Buffer.contents b
