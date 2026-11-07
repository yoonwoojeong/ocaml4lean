(* Two-tier hash-consing.

   The global tier is filled while the export file is parsed (single domain) and
   is frozen before checking starts; afterwards it is only read, which is safe to
   do concurrently.  Every checking domain has its own scratch tier, which is
   cleared after each declaration so that memory does not grow without bound.

   Invariant: a lookup always consults the global tier first, so within one
   domain two structurally equal values are physically equal.  Soundness never
   depends on this (we only ever conclude "equal" from [==], never "different"
   from [!=]), but caching and quick defeq checks rely on it for speed. *)

let frozen = ref false

let mix h x =
  let h = (h lxor x) * 0x100000001b3 in
  h lxor (h lsr 31)

module type S = sig
  type t
  val equal : t -> t -> bool   (* shallow: children compared with [==] *)
  val hash : t -> int
end

module Make (H : S) = struct
  module T = Hashtbl.Make (H)

  let global : H.t T.t = T.create 65536

  let local : H.t T.t Domain.DLS.key = Domain.DLS.new_key (fun () -> T.create 4096)

  let intern (x : H.t) : H.t =
    match T.find global x with
    | y -> y
    | exception Not_found ->
      if not !frozen then (T.add global x x; x)
      else begin
        let l = Domain.DLS.get local in
        match T.find l x with
        | y -> y
        | exception Not_found -> T.add l x x; x
      end

  let reset_local () =
    let l = Domain.DLS.get local in
    if T.length l > 0 then T.reset l

  let global_size () = T.length global
end
