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
  type t = { mutable hs : int array; mutable vs : H.t array; mutable n : int; mutable mask : int;
             dummy : H.t; mutable used : int array; track : bool }
  (* [used] records occupied slots (only for scratch tables, [track]) so that
     clearing costs O(entries) rather than O(capacity). *)

  let create ?(track = false) dummy cap =
    let cap = let c = ref 16 in while !c < 2 * cap do c := 2 * !c done; !c in
    { hs = Array.make cap 0; vs = Array.make cap dummy; n = 0; mask = cap - 1; dummy;
      used = (if track then Array.make 1024 0 else [||]); track }

  let key h = (h lor 1) land max_int     (* 0 marks an empty slot *)

  let find t (x : H.t) h =
    let hs = t.hs and mask = t.mask in
    let rec go i =
      let k = Array.unsafe_get hs i in
      if k = 0 then raise Not_found
      else if k = h && H.equal (Array.unsafe_get t.vs i) x then Array.unsafe_get t.vs i
      else go ((i + 1) land mask) in
    go (h land mask)

  (* returns the slot used *)
  let insert_raw hs vs mask h x =
    let rec go i = if Array.unsafe_get hs i = 0 then (Array.unsafe_set hs i h; Array.unsafe_set vs i x; i)
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
    let hs = Array.make cap 0 and vs = Array.make cap t.dummy in
    let mask = cap - 1 in
    let k = ref 0 in
    for i = 0 to t.mask do
      let h = t.hs.(i) in
      if h <> 0 then begin
        let j = insert_raw hs vs mask h t.vs.(i) in
        if t.track then (t.used.(!k) <- j; incr k)
      end
    done;
    t.hs <- hs; t.vs <- vs; t.mask <- mask

  let add t x h =
    if 2 * (t.n + 1) > t.mask + 1 then grow t;
    let i = insert_raw t.hs t.vs t.mask h x in
    record t i;
    t.n <- t.n + 1

  let clear t =
    if t.mask + 1 > 4096 then begin
      t.hs <- Array.make 4096 0; t.vs <- Array.make 4096 t.dummy; t.mask <- 4095
    end else if t.n > 0 then begin
      Array.fill t.hs 0 (t.mask + 1) 0; Array.fill t.vs 0 (t.mask + 1) t.dummy
    end;
    t.n <- 0
end

module Make (H : sig include S val dummy : t end) = struct
  module T = Set (H)

  let global = T.create H.dummy 65536
  let local : T.t Domain.DLS.key = Domain.DLS.new_key (fun () -> T.create H.dummy 4096)

  let intern_g try_global (x : H.t) : H.t =
    let h = T.key (H.hash x) in
    if not !frozen then
      (match T.find global x h with y -> y | exception Not_found -> T.add global x h; x)
    else begin
      match (if try_global then T.find global x h else raise Not_found) with
      | y -> y
      | exception Not_found ->
        let l = Domain.DLS.get local in
        match T.find l x h with
        | y -> y
        | exception Not_found -> T.add l x h; x
    end

  let intern x = intern_g true x

  let reset_local () = T.clear (Domain.DLS.get local)
  let global_size () = global.T.n
  let global_stats () = Printf.sprintf "n=%d slots=%d" global.T.n (global.T.mask + 1)
end
