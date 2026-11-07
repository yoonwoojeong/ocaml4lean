(* ocaml4lean: an external checker for Lean 4 export files.
   Exit codes: 0 accepted, 1 rejected, 2 usage/IO/parse error. *)
let () =
  let jobs = ref 1 and file = ref "" and stats = ref false and quiet = ref false in
  let spec = [
    ("-j", Arg.Set_int jobs, "N  number of checking domains (default 1)");
    ("--stats", Arg.Set stats, " print timing and GC statistics");
    ("-q", Arg.Set quiet, " only print the verdict");
  ] in
  Arg.parse spec (fun f -> file := f) "ocaml4lean [-j N] [--stats] FILE.ndjson  (FILE may be - for stdin)";
  if !file = "" then (prerr_endline "no input file"; exit 2);
  let t0 = Unix.gettimeofday () in
  (* Everything allocated while parsing stays live (it is the environment), so
     major collections during parsing are pure overhead. *)
  let gc0 = Gc.get () in
  Gc.set { gc0 with space_overhead = 10_000 };
  let env =
    try
      let ic = if !file = "-" then stdin else open_in_bin !file in
      let env = Kernel.Parse.read_channel ic in
      if !file <> "-" then close_in ic; env
    with
    | Kernel.Parse.Bad m -> Printf.printf "parse error: %s\n" m; exit 2
    | Sys_error m -> Printf.printf "error: %s\n" m; exit 2 in
  let t1 = Unix.gettimeofday () in
  Gc.set { gc0 with space_overhead = (match Sys.getenv_opt "O4L_SPACE_OVERHEAD" with Some v -> int_of_string v | None -> 120) };
  if !stats then Printf.eprintf "expr table: %s\n%!" (Kernel.Expr.H.global_stats ());
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
  | (_, m) :: _ ->
    Printf.printf "rejected (%d failing blocks): %s\n" (List.length r.errors) m; exit 1
