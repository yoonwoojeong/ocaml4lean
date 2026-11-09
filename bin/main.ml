(* ocaml4lean: an external checker for Lean 4 export files.
   Exit codes (as the lean-kernel-arena expects): 0 accepted, 1 rejected,
   3 error (usage, I/O, unparsable input, internal error).  Code 2 ("declined")
   is never used: the checker does not decline inputs. *)
(* Opt-in phase markers (O4L_MEMLOG=1): at each phase boundary print the
   kernel's view of memory (VmRSS, VmHWM from /proc/self/status) and the GC's.
   Continuous sampling is done from outside (bench/memprofile.sh): a monitoring
   domain would distort the measurement, since every domain takes part in
   OCaml 5's stop-the-world minor collections. *)
let memlog = Sys.getenv_opt "O4L_MEMLOG" <> None
let t_start = Unix.gettimeofday ()
let proc_kb field =
  try
    let ic = open_in "/proc/self/status" in
    let r = ref 0 in
    (try while true do
         let l = input_line ic in
         if String.length l > String.length field && String.sub l 0 (String.length field) = field then
           r := Scanf.sscanf (String.sub l (String.length field) (String.length l - String.length field)) " %d" (fun x -> x)
       done with End_of_file -> ());
    close_in ic; !r
  with _ -> 0
let proc_meminfo_mb field =
  try
    let ic = open_in "/proc/meminfo" in
    let r = ref 0 in
    (try while true do
         let l = input_line ic in
         if String.length l > String.length field && String.sub l 0 (String.length field) = field then
           r := Scanf.sscanf (String.sub l (String.length field) (String.length l - String.length field)) " %d" (fun x -> x) / 1024
       done with End_of_file -> ());
    close_in ic; !r
  with _ -> 0
let phase tag =
  if memlog then begin
    let s = Gc.quick_stat () in
    Printf.eprintf "memlog t=%.1f phase=%s rss=%dMB hwm=%dMB heap=%dMB top_heap=%dMB minor=%.0fMW promoted=%.0fMW major_gcs=%d\n%!"
      (Unix.gettimeofday () -. t_start) tag (proc_kb "VmRSS:" / 1024) (proc_kb "VmHWM:" / 1024)
      (s.heap_words * 8 / 1048576) (s.top_heap_words * 8 / 1048576)
      (s.minor_words /. 1e6) (s.promoted_words /. 1e6) s.major_collections
  end

let parse_only = ref false
let main () =
  let jobs = ref 1 and file = ref "" and stats = ref false and quiet = ref false in
  let spec = [
    ("-j", Arg.Set_int jobs, "N  number of checking domains (default 1)");
    ("--stats", Arg.Set stats, " print timing and GC statistics");
    ("-q", Arg.Set quiet, " only print the verdict");
    ("--parse-only", Arg.Set parse_only, " stop after parsing (for measurements)");
  ] in
  Arg.parse spec (fun f -> file := f) "ocaml4lean [-j N] [--stats] FILE.ndjson  (FILE may be - for stdin)";
  if !file = "" then (prerr_endline "no input file"; exit 3);
  let t0 = Unix.gettimeofday () in
  (* Memory policy.  The environment (about the size of the input file once
     parsed) stays live for the whole run, and OCaml's heap settles near
     live * (1 + space_overhead/100).  Small inputs use generous overheads,
     which are fastest; for inputs over 1 GB (Mathlib is ~6 GB) the overheads
     shrink and the heap is compacted after parsing, which discards the
     parser's garbage (measured on an 827 MB export: 1.38 GB heap after
     parsing, 0.87 GB live).  The env vars O4L_PARSE_OVERHEAD,
     O4L_SPACE_OVERHEAD and O4L_COMPACT=0/1 override the policy;
     O4L_DROP_TABLE=1 frees the hash-cons table after parsing (less memory,
     much slower; not used by default). *)
  let env_int v d = match Sys.getenv_opt v with Some x -> int_of_string x | None -> d in
  let input_mb = if !file = "-" then 0 else (try (Unix.stat !file).st_size / 1048576 with _ -> 0) in
  let gc0 = Gc.get () in
  Gc.set { gc0 with space_overhead = env_int "O4L_PARSE_OVERHEAD" (if input_mb <= 1024 then 200 else 80) };
  phase "parse-start";
  let env =
    try
      let ic = if !file = "-" then stdin else open_in_bin !file in
      let size_hint = if !file = "-" then 0 else input_mb * 1048576 in
      (* expressions are ~90% of the lines; after hash-consing ~90% remain *)
      Kernel.Expr.H.presize (size_hint / 52 * 8 / 10);
      let env = Kernel.Parse.read_channel ~size_hint ic in
      if !file <> "-" then close_in ic; env
    with
    | Kernel.Parse.Bad m -> Printf.printf "parse error: %s\n" m; exit 3
    | Sys_error m -> Printf.printf "error: %s\n" m; exit 3 in
  (* for stdin, estimate the size from the heap *)
  let input_mb = if !file = "-" then (Gc.quick_stat ()).heap_words * 8 / 1048576 / 2 else input_mb in
  if !stats then begin
    let s = Gc.quick_stat () in
    Printf.eprintf "after parse: heap %d MB, top_heap %d MB\n%!" (s.heap_words * 8 / 1048576) (s.top_heap_words * 8 / 1048576)
  end;
  phase "parse-end";
  if !parse_only then begin
    if !stats then Printf.eprintf "expr table: %s\n%!" (Kernel.Expr.H.global_stats ());
    Printf.printf "parsed\n"; exit 0
  end;
  if env_int "O4L_COMPACT" (if input_mb > 1024 then 1 else 0) = 1 then begin
    Gc.compact ();
    phase "compaction-end";
    if !stats then Printf.eprintf "after compaction: heap %d MB\n%!" ((Gc.quick_stat ()).heap_words * 8 / 1048576)
  end;
  let t1 = Unix.gettimeofday () in
  (* measured on an 827 MB export with this policy forced: overhead 25 gives a
     peak RSS of 2.1x the input (1.77 GB) for ~30% more check time.  Every
     major cycle marks the whole environment, so GC work grows as 1/overhead;
     when the budget leaves room, Check raises it to a floor of up to
     O4L_MIN_OVERHEAD (default 40), see its governor. *)
  let min_overhead = env_int "O4L_MIN_OVERHEAD" 40 in
  let overhead = env_int "O4L_SPACE_OVERHEAD" (if input_mb <= 1024 then 120 else max 25 (120 * 1024 / input_mb)) in
  if !stats then Printf.eprintf "space_overhead while checking: %d\n%!" overhead;
  Gc.set { gc0 with space_overhead = overhead };
  (* Memory budget for the governor (see Check): 80% of the cgroup limit or of
     physical memory (the official kernel itself peaks at 10.7 GB on the
     arena's 16 GB runner for Mathlib); O4L_MEM_BUDGET_MB overrides, 0
     disables. *)
  let budget_mb =
    let read_int f = try let ic = open_in f in let l = input_line ic in close_in ic; int_of_string (String.trim l) with _ -> 0 in
    let cgroup = read_int "/sys/fs/cgroup/memory.max" / 1048576 in
    let total = proc_meminfo_mb "MemTotal:" in
    let phys = if cgroup > 0 && (total = 0 || cgroup < total) then cgroup else total in
    match env_int "O4L_MEM_BUDGET_MB" (if phys > 0 then phys * 8 / 10 else 0) with 0 -> max_int | b -> b in
  if !stats then Printf.eprintf "memory budget: %d MB\n%!" budget_mb;
  if !stats then Printf.eprintf "expr table: %s\n%!" (Kernel.Expr.H.global_stats ());
  let ndecls = Kernel.Name.Tbl.length env.consts in
  let on_error i m =
    if not !quiet then
      Printf.eprintf "error in block %d (%s): %s\n%!" i
        (String.concat ", " (List.map Kernel.Name.to_string (Kernel.Env.block_names env.blocks.(i)))) m in
  phase "check-start";
  let r = Kernel.Check.run ~jobs:!jobs ~on_error ~budget_mb ~min_overhead ~log:memlog env in
  phase "check-end";
  let t2 = Unix.gettimeofday () in
  (* report axioms *)
  if not !quiet then begin
    let std = ["propext"; "Classical.choice"; "Quot.sound"] in
    Kernel.Name.Tbl.iter (fun _ (ci : Kernel.Env.cinfo) ->
        match ci.kind with
        | Kernel.Env.Axiom ->
          let n = Kernel.Name.to_string ci.name in
          if not (List.mem n std) then Printf.eprintf "note: non-standard axiom '%s'\n" n
        | _ -> ()) env.consts
  end;
  if !stats then begin
    let s = Gc.quick_stat () in
    Printf.eprintf "parse %.3fs  check %.3fs  total %.3fs  (%d constants, %d blocks, %d jobs)\n"
      (t1 -. t0) (t2 -. t1) (t2 -. t0) ndecls (Array.length env.blocks) !jobs;
    Printf.eprintf "gc: minor %.0f MW, promoted %.0f MW, major %.0f MW, minor_gcs %d, major_gcs %d, top_heap %d MB\n"
      (s.minor_words /. 1e6) (s.promoted_words /. 1e6) (s.major_words /. 1e6) s.minor_collections
      s.major_collections (s.top_heap_words * 8 / 1048576);
    if Kernel.Check.use_nbe then
      Printf.eprintf "nbe: accepted %d, declined %d, other fallbacks %d\n"
        (Atomic.get Kernel.Nbe.accepted) (Atomic.get Kernel.Nbe.declines) (Atomic.get Kernel.Nbe.fallbacks);
    Printf.eprintf "global hash-cons tables: exprs %d, levels %d, names %d\n"
      (Kernel.Expr.H.global_size ()) (Kernel.Level.H.global_size ()) (Kernel.Name.H.global_size ())
  end;
  match r.errors with
  | [] -> Printf.printf "accepted %d declarations\n" ndecls; exit 0
  | (_, m) :: _ when r.internal_only ->
    Printf.printf "error (%d blocks could not be checked): %s\n" (List.length r.errors) m; exit 3
  | (_, m) :: _ ->
    Printf.printf "rejected (%d failing blocks): %s\n" (List.length r.errors) m; exit 1

(* OCaml exits with code 2 on an uncaught exception, which the arena would
   read as "declined"; report every unexpected failure as an error instead. *)
let () =
  try main () with
  | Stdlib.Exit -> exit 3
  | e -> Printf.printf "internal error: %s\n%!" (Printexc.to_string e); exit 3
