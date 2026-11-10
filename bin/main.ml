(* ocaml4lean: an external checker for Lean 4 export files.
   Exit codes (as the lean-kernel-arena expects): 0 accepted, 1 rejected,
   3 error (usage, I/O, unparsable input, internal error).  Code 2 ("declined")
   is never used: the checker does not decline inputs. *)

(* Memory available to this process, in MB: the cgroup limit if there is one,
   else physical memory; 0 if neither can be read. *)
let memory_mb () =
  let first_line f = try let ic = open_in f in let l = input_line ic in close_in ic; Some l with _ -> None in
  let cgroup = match first_line "/sys/fs/cgroup/memory.max" with
    | Some l -> (try int_of_string (String.trim l) / 1048576 with _ -> 0)
    | None -> 0 in
  let total =
    try
      let ic = open_in "/proc/meminfo" in
      let r = ref 0 in
      (try while true do
           let l = input_line ic in
           if String.length l > 9 && String.sub l 0 9 = "MemTotal:" then
             r := Scanf.sscanf (String.sub l 9 (String.length l - 9)) " %d" (fun kb -> kb / 1024)
         done with End_of_file -> ());
      close_in ic; !r
    with _ -> 0 in
  if cgroup > 0 && (total = 0 || cgroup < total) then cgroup else total

let heap_mb () = (Gc.quick_stat ()).heap_words * 8 / 1048576

let main () =
  let jobs = ref 1 and file = ref "" and stats = ref false and quiet = ref false and parse_only = ref false in
  let spec = [
    ("-j", Arg.Set_int jobs, "N  number of checking domains (default 1)");
    ("--stats", Arg.Set stats, " print timing and GC statistics");
    ("-q", Arg.Set quiet, " only print the verdict");
    ("--parse-only", Arg.Set parse_only, " stop after parsing (for measurements)");
  ] in
  Arg.parse spec (fun f -> file := f) "ocaml4lean [-j N] [--stats] FILE.ndjson  (FILE may be - for stdin)";
  if !file = "" then (prerr_endline "no input file"; exit 3);
  let t0 = Unix.gettimeofday () in
  (* Memory rule (docs/DESIGN.md section 8).  The parsed environment stays
     live for the whole run and OCaml's heap settles near
     live * (1 + space_overhead / 100).  After parsing, the heap is compacted
     (the parser's garbage goes back to the OS and the live size L is known),
     and the overhead for checking is the largest value, within [25, 120], at
     which L * (1 + o/100) stays under 30% of the machine's memory.  The
     margin is measured: with 4 domains the peak resident set is about 1.8x
     that heap target (domains' working sets and garbage not yet collected).
     Nothing is adjusted later; running out of memory is an error (exit 3). *)
  let gc0 = Gc.get () in
  Gc.set { gc0 with space_overhead = 120 };
  let input_mb = if !file = "-" then 0 else (try (Unix.stat !file).st_size / 1048576 with _ -> 0) in
  let env =
    try
      let ic = if !file = "-" then stdin else open_in_bin !file in
      let size_hint = input_mb * 1048576 in
      (* expressions are ~90% of the lines; after hash-consing ~90% remain *)
      Kernel.Expr.H.presize (size_hint / 52 * 8 / 10);
      let env = Kernel.Parse.read_channel ~size_hint ic in
      if !file <> "-" then close_in ic; env
    with
    | Kernel.Parse.Bad m -> Printf.printf "parse error: %s\n" m; exit 3
    | Sys_error m -> Printf.printf "error: %s\n" m; exit 3 in
  if !stats then Printf.eprintf "after parse: heap %d MB, expr table: %s\n%!" (heap_mb ()) (Kernel.Expr.H.global_stats ());
  if !parse_only then (Printf.printf "parsed\n"; exit 0);
  Gc.compact ();
  let live_mb = heap_mb () and mem_mb = memory_mb () in
  let overhead = if mem_mb = 0 || live_mb = 0 then 120 else max 25 (min 120 (100 * (mem_mb * 3 / 10 - live_mb) / live_mb)) in
  Gc.set { gc0 with space_overhead = overhead };
  if !stats then Printf.eprintf "after compaction: live %d MB, memory %d MB, space_overhead %d\n%!" live_mb mem_mb overhead;
  let t1 = Unix.gettimeofday () in
  let ndecls = Kernel.Name.Tbl.length env.consts in
  let on_error i m =
    if not !quiet then
      Printf.eprintf "error in block %d (%s): %s\n%!" i
        (String.concat ", " (List.map Kernel.Name.to_string (Kernel.Env.block_names env.blocks.(i)))) m in
  let r = Kernel.Check.run ~jobs:!jobs ~on_error env in
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
    Printf.eprintf "global hash-cons tables: exprs %d, levels %d, names %d\n"
      (Kernel.Expr.H.global_size ()) (Kernel.Level.H.global_size ()) (Kernel.Name.H.global_size ())
  end;
  match r.errors with
  | [] -> Printf.printf "accepted %d declarations\n" ndecls; exit 0
  | (_, m) :: _ when r.internal_only ->
    Printf.printf "error (a block could not be checked): %s\n" m; exit 3
  | (_, m) :: _ ->
    Printf.printf "rejected: %s\n" m; exit 1

(* OCaml exits with code 2 on an uncaught exception, which the arena would
   read as "declined"; report every unexpected failure as an error instead. *)
let () =
  try main () with
  | Stdlib.Exit -> exit 3
  | e -> Printf.printf "internal error: %s\n%!" (Printexc.to_string e); exit 3
