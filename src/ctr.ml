(* Performance counters, for analysis only.

   [enabled] is a compile-time constant: `O4L_COUNTERS=1 ./build.sh` builds
   with it set to true; a normal build has it false, and the compiler drops
   every [if enabled then ...] (checked in the generated code), so counters
   cost nothing and cannot affect checking.  Counters never influence a
   result: they are only written, and read once at exit.

   Each domain counts in its own row of one flat array (padded to separate
   cache lines), so increments need no atomics; [report] sums the rows. *)

let enabled = false

let names = [| "infer"; "infer.hit"; "whnf"; "whnf.hit"; "whnf_core"; "whnf_core.hit";
               "session.lookup"; "session.hit"; "defeq"; "defeq.quick"; "defeq.lazy_delta";
               "delta.step"; "unfold.inst"; "instantiate"; "instantiate.node" |]
let infer = 0 and infer_hit = 1 and whnf = 2 and whnf_hit = 3 and whnf_core = 4
and whnf_core_hit = 5 and sess_lookup = 6 and sess_hit = 7 and defeq = 8 and defeq_quick = 9
and defeq_lazy = 10 and delta_step = 11 and unfold_inst = 12 and instantiate = 13
and inst_node = 14

let n = Array.length names
let stride = (n + 8) land lnot 7          (* row width, a multiple of 64 bytes *)
let rows = 64                              (* domain ids are taken mod rows *)
let tbl = if enabled then Array.make (rows * stride) 0 else [||]

let[@inline] incr k =
  if enabled then begin
    let i = ((Domain.self () :> int) land (rows - 1)) * stride + k in
    Array.unsafe_set tbl i (Array.unsafe_get tbl i + 1)
  end

let report oc =
  if enabled then begin
    let sum k = let s = ref 0 in for r = 0 to rows - 1 do s := !s + tbl.(r * stride + k) done; !s in
    Array.iteri (fun k nm -> Printf.fprintf oc "counter %-18s %14d\n" nm (sum k)) names;
    flush oc
  end
