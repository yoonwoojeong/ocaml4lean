(* Two-tier hash-consing.

   The global tier is filled while the export file is parsed (single domain) and
   is frozen before checking starts; afterwards it is only read, which is safe to
   do concurrently.  Every checking domain has its own scratch tier, which is
   cleared after each declaration so that memory does not grow without bound.

   Invariant: a lookup always consults the global tier first (unless the value
   provably cannot be there), so within one domain two structurally equal values
   are physically equal.  Soundness never depends on this (we only ever
   conclude "equal" from [==], never "different" from [!=]); caching and quick
   definitional-equality checks rely on it for speed. *)

let frozen = ref false

let mix h x =
  let h = (h lxor x) * 0x100000001b3 in
  h lxor (h lsr 31)

module type S = sig
  type t
  val equal : t -> t -> bool   (* shallow: children compared with [==] *)
  val hash : t -> int
end

(* Open-addressing hash set with linear probing.  Hashes are kept in a flat
   int array so that probing touches values only on a hash match. *)
module Set (H : S) = struct
  (* Hashes live in an off-heap 32-bit Bigarray: half the size of an int
     array, and never scanned by the GC (the environment's table is large). *)
  type hs = (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t
  let hs_make n : hs = let a = Bigarray.Array1.create Bigarray.int32 Bigarray.c_layout n in Bigarray.Array1.fill a 0l; a
  let hs_get (a : hs) i = Int32.to_int (Bigarray.Array1.unsafe_get a i)
  let hs_set (a : hs) i v = Bigarray.Array1.unsafe_set a i (Int32.of_int v)

  type t = { mutable hs : hs; mutable vs : H.t array; mutable n : int; mutable mask : int;
             dummy : H.t; mutable used : int array; track : bool }
  (* [used] records occupied slots (only for scratch tables, [track]) so that
     clearing costs O(entries) rather than O(capacity). *)

  (* capacity: smallest power of two holding [cap] entries below 3/4 load *)
  let create ?(track = false) dummy cap =
    let cap = let c = ref 16 in while 3 * !c < 4 * (cap + 1) do c := 2 * !c done; !c in
    { hs = hs_make cap; vs = Array.make cap dummy; n = 0; mask = cap - 1; dummy;
      used = (if track then Array.make 1024 0 else [||]); track }

  let key h = (h land 0x3FFFFFFF) lor 1     (* fits int32; 0 marks an empty slot *)

  let find t (x : H.t) h =
    let hs = t.hs and mask = t.mask in
    let rec go i =
      let k = hs_get hs i in
      if k = 0 then raise Not_found
      else if k = h && H.equal (Array.unsafe_get t.vs i) x then Array.unsafe_get t.vs i
      else go ((i + 1) land mask) in
    go (h land mask)

  (* returns the slot used *)
  let insert_raw hs vs mask h x =
    let rec go i = if hs_get hs i = 0 then (hs_set hs i h; Array.unsafe_set vs i x; i)
      else go ((i + 1) land mask) in
    go (h land mask)

  let record t i =
    if t.track then begin
      if t.n >= Array.length t.used then begin
        let u = Array.make (2 * Array.length t.used) 0 in
        Array.blit t.used 0 u 0 (Array.length t.used); t.used <- u
      end;
      Array.unsafe_set t.used t.n i
    end

  let grow t =
    let cap = 2 * (t.mask + 1) in
    let hs = hs_make cap and vs = Array.make cap t.dummy in
    let mask = cap - 1 in
    let k = ref 0 in
    for i = 0 to t.mask do
      let h = hs_get t.hs i in
      if h <> 0 then begin
        let j = insert_raw hs vs mask h t.vs.(i) in
        if t.track then (t.used.(!k) <- j; incr k)
      end
    done;
    t.hs <- hs; t.vs <- vs; t.mask <- mask

  let add t x h =
    (* grow at 3/4 load: the environment's table is the largest structure *)
    if 4 * (t.n + 1) > 3 * (t.mask + 1) then grow t;
    let i = insert_raw t.hs t.vs t.mask h x in
    record t i;
    t.n <- t.n + 1

  let clear t =
    if t.mask + 1 > 4096 then begin
      t.hs <- hs_make 4096; t.vs <- Array.make 4096 t.dummy; t.mask <- 4095
    end else if t.n > 0 then begin
      Bigarray.Array1.fill t.hs 0l; Array.fill t.vs 0 (t.mask + 1) t.dummy
    end;
    t.n <- 0
end

module Make (H : sig include S val dummy : t end) = struct
  module T = Set (H)

  let global = T.create H.dummy 65536
  (* Size the table for [n] entries up front (call before parsing): growing it
     copies the arrays, with old and new alive at once and the old ones left as
     garbage -- the largest transient of parsing a big environment. *)
  let presize n =
    if n > global.T.n && 4 * n > 3 * (global.T.mask + 1) then begin
      let fresh = T.create H.dummy n in
      for i = 0 to global.T.mask do
        let h = T.hs_get global.T.hs i in
        if h <> 0 then T.add fresh global.T.vs.(i) h
      done;
      global.T.hs <- fresh.T.hs; global.T.vs <- fresh.T.vs; global.T.mask <- fresh.T.mask; global.T.n <- fresh.T.n
    end
  let global_n = ref 0
  (* After parsing, the table is only needed for an optional sharing lookup;
     dropping it frees several words per environment node.  The global nodes
     remain canonical (they were deduplicated while parsing), which is all
     that equality relies on. *)
  let lookups = ref true
  let drop_global () =
    global_n := global.T.n;
    lookups := false;
    global.T.hs <- T.hs_make 1; global.T.vs <- [| H.dummy |]; global.T.mask <- 0; global.T.n <- 0
  let local : T.t Domain.DLS.key = Domain.DLS.new_key (fun () -> T.create H.dummy 4096)

  (* After parsing, values not found in the (frozen) global tier are simply
     returned unshared: maintaining a mutable scratch tier costs more (write
     barriers, table growth, GC marking) than sharing saves.  [try_global] is
     false when the value cannot be in the global tier (some child is not). *)
  let intern_g try_global (x : H.t) : H.t =
    let h = T.key (H.hash x) in
    if not !frozen then
      (match T.find global x h with y -> y | exception Not_found -> T.add global x h; x)
    else if try_global && !lookups then
      (match T.find global x h with y -> y | exception Not_found -> x)
    else x

  (* Names and levels are few: keep a per-domain scratch tier for them so that
     they stay canonical (level normalisation compares them physically). *)
  let intern_local (x : H.t) : H.t =
    let h = T.key (H.hash x) in
    if not !frozen then
      (match T.find global x h with y -> y | exception Not_found -> T.add global x h; x)
    else begin
      match T.find global x h with
      | y -> y
      | exception Not_found ->
        let l = Domain.DLS.get local in
        match T.find l x h with
        | y -> y
        | exception Not_found -> T.add l x h; x
    end

  let intern x = intern_local x

  let reset_local () = T.clear (Domain.DLS.get local)
  let global_size () = max global.T.n !global_n
  let global_stats () = Printf.sprintf "n=%d slots=%d" global.T.n (global.T.mask + 1)
end
