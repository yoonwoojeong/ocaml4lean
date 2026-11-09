(* Checking an environment: one block at a time, blocks in parallel. *)
open Env
open Tc

let rec dup_names = function [] -> None | x :: r -> if List.exists (Name.equal x) r then Some x else dup_names r

let check_lparams (ci : cinfo) =
  match dup_names ci.lparams with
  | Some n -> fail "duplicate universe level parameter '%s'" (Name.to_string n)
  | None -> ()

let expr_equal = Expr.equal

let names_equal a b = List.length a = List.length b && List.for_all2 Name.equal a b

let with_lparams c (ci : cinfo) f = c.lparams <- Some ci.lparams; let r = f () in c.lparams <- None; r

(* check type of a constant: well-formed and a sort *)
let check_type c (ci : cinfo) =
  check_lparams ci;
  with_lparams c ci (fun () -> ignore (Tc.ensure_sort c (Tc.check c ci.ty)))

let check_value c (ci : cinfo) v =
  let vt = with_lparams c ci (fun () -> Tc.check c v) in
  if not (Tc.is_def_eq c vt ci.ty) then
    fail "type mismatch in declaration '%s'" (Name.to_string ci.name)

(* ---------------------------------------------------------------- quot *)
let check_quot env bi pos (l : cinfo list) =
  let c = Tc.create env bi pos in
  (* Eq must be the expected inductive type *)
  let eq = match Tc.find c N.eq with
    | Some ({ kind = Induct { ctors = [refl]; _ }; lparams = [_]; _ } as ci) -> (ci, refl)
    | _ -> fail "failed to initialize quot module, environment does not have a suitable 'Eq' type" in
  let open Expr in
  let (eq_ci, refl) = eq in
  let u_eq = Level.param (List.hd eq_ci.lparams) in
  (* Eq : {α : Sort u} → α → α → Prop *)
  if not (expr_equal eq_ci.ty (pi (sort u_eq) (pi (bvar 0) (pi (bvar 1) (sort Level.zero))))) then
    fail "failed to initialize quot module, 'Eq' has an unexpected type";
  (match Tc.find c refl with
   | Some ({ lparams = [v]; kind = Ctor _; _ } as rci) when Name.equal refl N.eq_refl ->
     let u = Level.param v in
     if not (expr_equal rci.ty (pi (sort u) (pi (bvar 0) (app (app (app (const N.eq [u]) (bvar 1)) (bvar 0)) (bvar 0))))) then
       fail "failed to initialize quot module, unexpected type for 'Eq.refl'"
   | _ -> fail "failed to initialize quot module, unexpected 'Eq' constructor");
  let un = Name.of_string "u" and vn = Name.of_string "v" in
  let u = Level.param un and v = Level.param vn in
  let prop = sort Level.zero in
  (* {α : Sort u} → (r : α → α → Prop) → Sort u *)
  let rel a = pi a (pi (lift_loose a 0 1) prop) in
  let quot_ty = pi (sort u) (pi (rel (bvar 0)) (sort u)) in
  let quot_app a r = app (app (const N.quot [u]) a) r in
  (* {α} → (r) → α → Quot r *)
  let mk_ty = pi (sort u) (pi (rel (bvar 0)) (pi (bvar 1) (quot_app (bvar 2) (bvar 1)))) in
  (* {α} {r} {β : Sort v} (f : α → β) : (∀ a b, r a b → f a = f b) → Quot r → β *)
  let lift_ty =
    pi (sort u) (pi (rel (bvar 0)) (pi (sort v) (pi (pi (bvar 2) (bvar 1))
      (pi (pi (bvar 3) (pi (bvar 4) (pi (app (app (bvar 4) (bvar 1)) (bvar 0))
                                     (app (app (app (const N.eq [v]) (bvar 4)) (app (bvar 3) (bvar 2))) (app (bvar 3) (bvar 1))))))
         (pi (quot_app (bvar 4) (bvar 3)) (bvar 3)))))) in
  (* {α} {r} {β : Quot r → Prop} : (∀ a, β (Quot.mk r a)) → ∀ q, β q *)
  let mk_app_ a r x = app (app (app (const N.quot_mk [u]) a) r) x in
  let ind_ty =
    pi (sort u) (pi (rel (bvar 0)) (pi (pi (quot_app (bvar 1) (bvar 0)) prop)
      (pi (pi (bvar 2) (app (bvar 1) (mk_app_ (bvar 3) (bvar 2) (bvar 0))))
         (pi (quot_app (bvar 3) (bvar 2)) (app (bvar 2) (bvar 0)))))) in
  let expect = [ (N.quot, QType, [un], quot_ty); (N.quot_mk, QCtor, [un], mk_ty);
                 (N.quot_lift, QLift, [un; vn], lift_ty); (N.quot_ind, QInd, [un], ind_ty) ] in
  if List.length l <> 4 then fail "quotient block must declare exactly Quot, Quot.mk, Quot.lift, Quot.ind";
  List.iter (fun (n, k, lps, ty) ->
      match List.find_opt (fun (ci : cinfo) -> Name.equal ci.name n) l with
      | Some ci when ci.kind = Quot k && names_equal ci.lparams lps && expr_equal ci.ty ty -> ()
      | _ -> fail "unexpected quotient declaration '%s'" (Name.to_string n)) expect

(* ----------------------------------------------------------- inductives *)
let kind_equal a b = match a, b with
  | Induct x, Induct y ->
    x.nparams = y.nparams && x.nindices = y.nindices && names_equal x.all y.all &&
    names_equal x.ctors y.ctors && x.nnested = y.nnested && x.is_rec = y.is_rec && x.is_reflexive = y.is_reflexive
  | Ctor x, Ctor y -> Name.equal x.induct y.induct && x.cidx = y.cidx && x.cnparams = y.cnparams && x.nfields = y.nfields
  | Recursor x, Recursor y ->
    names_equal x.rall y.rall && x.rnparams = y.rnparams && x.rnindices = y.rnindices &&
    x.nmotives = y.nmotives && x.nminors = y.nminors && x.k = y.k &&
    List.length x.rules = List.length y.rules &&
    List.for_all2 (fun r s -> Name.equal r.r_ctor s.r_ctor && r.r_nfields = s.r_nfields && expr_equal r.r_rhs s.r_rhs)
      x.rules y.rules
  | _ -> false

(* Universe parameter names are binders: compare modulo a positional renaming
   (the kernel calls the eliminator universe `u`, other producers may not). *)
let rename_lparams (g : cinfo) (target : Name.t list) =
  if names_equal g.lparams target || List.length g.lparams <> List.length target
     || dup_names target <> None then g
  else begin
    let ls = List.map Level.param target in
    let inst e = Expr.instantiate_lparams e g.lparams ls in
    let kind = match g.kind with
      | Recursor r -> Recursor { r with rules = List.map (fun rl -> { rl with r_rhs = inst rl.r_rhs }) r.rules }
      | k -> k in
    { g with lparams = target; ty = inst g.ty; kind }
  end

let same_decl what (g : cinfo) (e : cinfo) =
  let g = rename_lparams g e.lparams in
  if not (Name.equal g.name e.name && names_equal g.lparams e.lparams && g.unsafe = e.unsafe) then
    fail "exported %s '%s' does not match the derived one (name, universe parameters or safety)" what (Name.to_string e.name);
  if not (expr_equal g.ty e.ty) then begin
    if Sys.getenv_opt "O4L_DEBUG" <> None then
      Printf.eprintf "derived:  %s\nexported: %s\n" (Expr.to_string ~max:100000 g.ty) (Expr.to_string ~max:100000 e.ty);
    fail "exported %s '%s' has a type different from the derived one" what (Name.to_string e.name)
  end;
  if not (kind_equal g.kind e.kind) then begin
    if Sys.getenv_opt "O4L_DEBUG" <> None then begin
      let show = function
        | Recursor r -> Printf.sprintf "all=[%s] np=%d ni=%d nmot=%d nmin=%d k=%b rules=[%s]"
                          (String.concat "," (List.map Name.to_string r.rall)) r.rnparams r.rnindices r.nmotives r.nminors r.k
                          (String.concat "; " (List.map (fun rl -> Name.to_string rl.r_ctor ^ "/" ^ string_of_int rl.r_nfields ^ ": " ^ Expr.to_string rl.r_rhs) r.rules))
        | Induct i -> Printf.sprintf "np=%d ni=%d all=[%s] ctors=[%s] nnested=%d rec=%b refl=%b" i.nparams i.nindices
                        (String.concat "," (List.map Name.to_string i.all)) (String.concat "," (List.map Name.to_string i.ctors)) i.nnested i.is_rec i.is_reflexive
        | Ctor c -> Printf.sprintf "induct=%s cidx=%d np=%d nf=%d" (Name.to_string c.induct) c.cidx c.cnparams c.nfields
        | _ -> "?" in
      Printf.eprintf "derived:  %s\nexported: %s\n" (show g.kind) (show e.kind)
    end;
    fail "exported %s '%s' differs from the derived one" what (Name.to_string e.name)
  end

let check_ind_block env bi pos types ctors recs =
  let open Inductive in
  let first = match types with t :: _ -> t | [] -> fail "empty inductive block" in
  let nparams = match first.kind with Induct iv -> iv.nparams | _ -> assert false in
  let d_types = List.map (fun (t : cinfo) ->
      match t.kind with
      | Induct iv ->
        { it_name = t.name; it_ty = t.ty;
          it_ctors = List.map (fun cn ->
              match List.find_opt (fun (c : cinfo) -> Name.equal c.name cn) ctors with
              | Some c -> (cn, c.ty)
              | None -> fail "constructor '%s' of '%s' is missing" (Name.to_string cn) (Name.to_string t.name))
              iv.ctors }
      | _ -> assert false) types in
  let d = { d_lparams = first.lparams; d_nparams = nparams; d_types; d_unsafe = first.unsafe } in
  let g = Inductive.add_inductive env bi pos d in
  (* Exporters may list the members of a block in any order (lean4export
     collects recursors in a name set), so they are matched by name; every
     exported member must correspond to exactly one derived one. *)
  let match_lists what (gen : cinfo list) (exp : cinfo list) =
    if List.length gen <> List.length exp then
      fail "inductive block of '%s': expected %d %s, export has %d" (Name.to_string first.name)
        (List.length gen) what (List.length exp);
    List.iter (fun (e : cinfo) ->
        match List.filter (fun (g : cinfo) -> Name.equal g.name e.name) gen with
        | [g] -> same_decl what g e
        | _ -> fail "exported %s '%s' is not derived from its inductive block" what (Name.to_string e.name))
      exp in
  match_lists "types" g.g_types types;
  match_lists "constructors" g.g_ctors ctors;
  match_lists "recursors" g.g_recs recs

(* ---------------------------------------------------------------- blocks *)
let check_block env bi pos (b : block) =
  match b with
  | Single ci ->
    (match ci.kind with
     | Axiom ->
       let c = Tc.create ~safety:(if ci.unsafe then Unsafe else Safe) env bi pos in
       check_type c ci
     | Thm { value; _ } ->
       let c = Tc.create env bi pos in
       check_type c ci;
       if not (Tc.is_prop c ci.ty) then fail "theorem '%s' type is not a proposition" (Name.to_string ci.name);
       check_value c ci value
     | Opaq { value; _ } ->
       let c = Tc.create ~safety:(if ci.unsafe then Unsafe else Safe) env bi pos in
       check_type c ci;
       check_value c ci value
     | Defn { value; safety; all; _ } ->
       (match safety with
        | Safe ->
          let c = Tc.create env bi pos in
          check_type c ci; check_value c ci value
        | _ ->
          (* unsafe or mutual partial: the header is checked first, then the
             body may refer to the declaration itself and its mutual group *)
          let c0 = Tc.create ~safety env bi pos in
          check_type c0 ci;
          let local = Name.Tbl.create 8 in
          Name.Tbl.replace local ci.name ci;
          List.iter (fun n ->
              match Name.Tbl.find_opt env.consts n with
              | Some ({ kind = Defn { safety = s; _ }; _ } as m) when s = safety && names_equal m.lparams ci.lparams ->
                Name.Tbl.replace local n m
              | _ -> ()) all;
          let c = Tc.create ~local ~safety env bi pos in
          check_value c ci value)
     | Quot _ | Induct _ | Ctor _ | Recursor _ -> fail "misplaced declaration '%s'" (Name.to_string ci.name))
  | QuotBlock l -> check_quot env bi pos l
  | IndBlock { types; ctors; recs } -> check_ind_block env bi pos types ctors recs

(* ------------------------------------------------------------- builtins *)
(* The Nat/String literal extensions are only sound if the relevant names
   denote the expected inductive types.  (As in the official kernel, the
   arithmetic functions Nat.add, ... are trusted to be the standard ones.) *)
let builtins (env : Env.t) =
  let open Expr in
  let get n = Name.Tbl.find_opt env.consts (Name.of_string n) in
  let nat = const (Name.of_string "Nat") [] in
  let ind_ok n lps ty ctors = match get n with
    | Some { kind = Induct iv; ty = t; lparams; unsafe = false; _ } ->
      List.length lparams = lps && expr_equal t ty &&
      names_equal iv.ctors (List.map Name.of_string ctors)
    | _ -> false in
  let ty_ok n ty = match get n with Some ci -> ci.lparams = [] && expr_equal ci.ty ty && not ci.unsafe | None -> false in
  let typ = sort Level.one in
  let bool = const (Name.of_string "Bool") [] in
  let bool_ok () =
    ind_ok "Bool" 0 typ ["Bool.false"; "Bool.true"] && ty_ok "Bool.false" bool && ty_ok "Bool.true" bool in
  let nat_ok =
    ind_ok "Nat" 0 typ ["Nat.zero"; "Nat.succ"] &&
    ty_ok "Nat.zero" nat && ty_ok "Nat.succ" (pi nat nat) &&
    List.for_all (fun (n, r) -> match get n with
        | None -> true
        | Some _ -> ty_ok n (pi nat (pi nat r)) && (r != bool || bool_ok ()))
      [ ("Nat.add", nat); ("Nat.sub", nat); ("Nat.mul", nat); ("Nat.pow", nat); ("Nat.gcd", nat);
        ("Nat.mod", nat); ("Nat.div", nat); ("Nat.beq", bool); ("Nat.ble", bool); ("Nat.land", nat);
        ("Nat.lor", nat); ("Nat.xor", nat); ("Nat.shiftLeft", nat); ("Nat.shiftRight", nat) ] in
  let char = const (Name.of_string "Char") [] in
  let list_char = app (const (Name.of_string "List") [Level.zero]) char in
  let str_ok = nat_ok &&
    ty_ok "String.ofList" (pi list_char (const (Name.of_string "String") [])) &&
    ty_ok "Char.ofNat" (pi nat char) &&
    (match get "List" with
     | Some { kind = Induct { ctors; nparams = 1; nindices = 0; _ }; lparams = [_]; _ } ->
       names_equal ctors [Name.of_string "List.nil"; Name.of_string "List.cons"]
     | _ -> false) in
  { nat_ok; str_ok; quot_ok = true }

(* ---------------------------------------------------------------- driver *)
type result = { errors : (int * string) list; checked : int; internal_only : bool }
(* [internal_only]: every failure was an internal error (no kernel verdict) *)

let reset_scratch () = Name.H.reset_local (); Level.H.reset_local (); Expr.H.reset_local ()

(* ------------------------------------------------------------ governor *)
(* Memory governor.  Peak memory depends on the input's shape (how large the
   declarations being checked at the same time are) and, with several domains,
   includes per-domain memory the GC does not account for (allocator slack,
   free per-domain pools, stacks) -- measured: 0.16 GB above the heap with one
   domain, 0.7 GB with four on an 827 MB input.  So the governor watches the
   real resident set (VmRSS) and, while it is above the budget, lowers the GC
   space overhead (never below a floor derived from the headroom, see [run]) and lets fewer domains start
   new declarations (never fewer than one).  It only changes scheduling and GC
   pacing, never what is checked.

   Relief is judged against the headroom above the live heap at the start of
   checking ([base_heap], essentially the environment, which stays live to the
   end): the heap must be within 60% of [base_heap .. budget].  An absolute
   threshold (60% of the budget) can never be met once the environment alone
   is that large -- on the arena's Mathlib (about 6 GB of environment against
   a 9.4 GB budget) the governor stayed at one domain and space overhead 10
   for the whole run, 4.4x the official kernel's instructions.  The overhead
   floor matters for the same reason: every major cycle marks the whole
   environment, so GC work grows as 1/overhead. *)
let rss_mb () =
  try
    let ic = open_in "/proc/self/status" in
    let r = ref 0 in
    (try while true do
         let l = input_line ic in
         if String.length l > 6 && String.sub l 0 6 = "VmRSS:" then
           r := Scanf.sscanf (String.sub l 6 (String.length l - 6)) " %d" (fun x -> x / 1024)
       done with End_of_file -> ());
    close_in ic; !r
  with _ -> 0

type governor = {
  budget_mb : int;
  base_heap : int;                 (* GC heap (MB) when checking starts *)
  base_overhead : int;
  min_overhead : int;
  max_jobs : int;
  allowed : int Atomic.t;          (* workers with id < allowed may start a block *)
  busy : bool Atomic.t;            (* one worker samples at a time *)
  next_sample : float Atomic.t;
  mutable overhead : int;
  mutable last_rss : int;          (* highest RSS seen at a sample *)
  log : bool;
}

let governor_sample g =
  let now = Unix.gettimeofday () in
  if now >= Atomic.get g.next_sample && Atomic.compare_and_set g.busy false true then begin
    Atomic.set g.next_sample (now +. 0.2);
    let rss = rss_mb () in
    let heap = (Gc.quick_stat ()).heap_words * 8 / 1048576 in   (* all domains *)
    let grew = rss > g.last_rss + 32 in
    g.last_rss <- max g.last_rss rss;
    let a = Atomic.get g.allowed in
    (* RSS is a high-water mark (OCaml 5 keeps freed pool memory mapped), so
       pressure means: above budget and still growing, or the GC heap itself
       close to the budget.  Relief is judged on the GC heap: well below the
       budget means the memory already mapped has room to be reused. *)
    let pressure = (rss > g.budget_mb && grew) || heap > g.budget_mb * 9 / 10 in
    let headroom = max 0 (g.budget_mb - g.base_heap) in
    let relief = heap < g.base_heap + headroom * 6 / 10 && not grew in
    let a', o' =
      if pressure then max 1 (a - 1), max g.min_overhead (g.overhead * 2 / 3)
      else if relief then min g.max_jobs (a + 1), min g.base_overhead (g.overhead * 3 / 2 + 1)
      else a, g.overhead in
    if o' <> g.overhead then begin
      g.overhead <- o';
      Gc.set { (Gc.get ()) with space_overhead = o' }
    end;
    if a' <> a then Atomic.set g.allowed a';
    if g.log && (a' <> a || o' <> g.overhead || pressure) then
      Printf.eprintf "memlog governor rss=%dMB heap=%dMB budget=%dMB domains=%d space_overhead=%d\n%!"
        rss heap g.budget_mb a' g.overhead;
    Atomic.set g.busy false
  end

let run ?(jobs = 1) ?(on_error = fun _ _ -> ()) ?(budget_mb = max_int) ?(min_overhead = 40)
    ?(log = false) (env : Env.t) =
  Hc.frozen := true;
  let bi = builtins env in
  let nb = Array.length env.blocks in
  let errs = Array.make nb None in
  let times = Array.make nb 0.0 in
  let internal = Array.make nb false in
  let timing = Sys.getenv_opt "O4L_TIMES" <> None in
  let next = Atomic.make 0 in
  (* Overhead floor: the largest overhead (at most [min_overhead]) whose
     steady heap, base_heap * (1 + o/100), fits in 3/4 of the budget, but
     never below 10.  When the floor is above the size-based policy the
     checking starts at the floor: more memory that is available anyway, less
     re-marking of the environment. *)
  let base_heap = (Gc.quick_stat ()).heap_words * 8 / 1048576 in
  let governed = budget_mb < max_int in
  let floor =
    if not governed || base_heap <= 0 then min_overhead
    else max 10 (min min_overhead (100 * (budget_mb * 3 / 4 - base_heap) / base_heap)) in
  let base_overhead =
    let o = (Gc.get ()).space_overhead in
    if governed && o < floor then (Gc.set { (Gc.get ()) with space_overhead = floor }; floor) else o in
  if log then Printf.eprintf "memlog governor-start base_heap=%dMB budget=%dMB floor=%d overhead=%d\n%!"
      base_heap budget_mb floor base_overhead;
  let g = { budget_mb; base_heap; base_overhead; min_overhead = min base_overhead floor; max_jobs = max 1 jobs;
            allowed = Atomic.make (max 1 jobs); busy = Atomic.make false;
            next_sample = Atomic.make 0.0; overhead = (Gc.get ()).space_overhead; last_rss = 0; log } in
  let worker w () =
    let rec loop () =
      if governed then begin
        governor_sample g;
        (* paused while the governor allows fewer domains (worker 0 never is) *)
        while w >= Atomic.get g.allowed && Atomic.get next < nb do
          Unix.sleepf 0.05; governor_sample g
        done
      end;
      let i = Atomic.fetch_and_add next 1 in
      if i < nb then begin
        let t0 = if timing then Unix.gettimeofday () else 0.0 in
        (try check_block env bi i env.blocks.(i) with
         | Kernel_error m -> errs.(i) <- Some m
         | e ->
           (* not a verdict about the input: a resource limit or a bug *)
           let m = match e with
             | Stack_overflow -> "stack overflow" | Out_of_memory -> "out of memory"
             | e -> Printexc.to_string e in
           internal.(i) <- true;
           errs.(i) <- Some ("internal error: " ^ m));
        if timing then times.(i) <- Unix.gettimeofday () -. t0;
        (match errs.(i) with Some m -> on_error i m | None -> ());
        reset_scratch ();
        loop ()
      end in
    loop () in
  if jobs <= 1 then worker 0 ()
  else begin
    let ds = List.init (jobs - 1) (fun k -> Domain.spawn (worker (k + 1))) in
    worker 0 ();
    List.iter Domain.join ds
  end;
  if timing then begin
    let idx = Array.init nb (fun i -> i) in
    Array.sort (fun a b -> compare times.(b) times.(a)) idx;
    let tot = Array.fold_left (+.) 0.0 times in
    Printf.eprintf "total block time %.2fs; slowest:\n" tot;
    for k = 0 to min 24 (nb - 1) do
      let i = idx.(k) in
      Printf.eprintf "  %7.3fs  %s\n" times.(i) (String.concat ", " (List.map Name.to_string (block_names env.blocks.(i))))
    done
  end;
  let errors = ref [] in
  for i = nb - 1 downto 0 do match errs.(i) with Some m -> errors := (i, m) :: !errors | None -> () done;
  let errors = List.map (fun n -> (-1, "duplicate declaration '" ^ Name.to_string n ^ "'")) env.dups @ !errors in
  let internal_only = errors <> [] && env.dups = [] &&
                      Array.for_all2 (fun e int -> e = None || int) errs internal in
  { errors; checked = nb; internal_only }
