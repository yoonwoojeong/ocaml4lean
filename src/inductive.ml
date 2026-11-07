(* Checking of (mutual, nested) inductive declarations.

   We re-derive everything the kernel would derive from the inductive types and
   their constructors -- the inductive/constructor metadata and the recursors
   with their computation rules -- following Lean's kernel/inductive.cpp, and
   then require the exported declarations to be identical to the derived ones.
   Hence nothing in an exported inductive block is trusted. *)
open Expr
open Env
open Tc

type ind_type = { it_name : Name.t; it_ty : Expr.t; it_ctors : (Name.t * Expr.t) list }
type decl = { d_lparams : Name.t list; d_nparams : int; d_types : ind_type list; d_unsafe : bool }

let n_nested = Name.str Name.Anon "_nested"
let rec_name n = Name.str n "rec"

(* Lean's Expr.consumeTypeAnnotations *)
let rec consume_type_annotations e =
  let fn, args = get_app_args e in
  match fn with
  | Const { n; _ } ->
    let s = Name.to_string n in
    if (s = "optParam" || s = "autoParam") && Array.length args = 2 then consume_type_annotations args.(0)
    else if (s = "outParam" || s = "semiOutParam") && Array.length args = 1 then consume_type_annotations args.(0)
    else e
  | _ -> e

let local_for = function
  | Pi { ty; _ } | Lam { ty; _ } -> mk_fvar (consume_type_annotations ty)
  | _ -> assert false
let mk_local ty = mk_fvar (consume_type_annotations ty)

let binding_body = function Pi { b; _ } | Lam { b; _ } -> b | _ -> assert false
let binding_domain = function Pi { ty; _ } | Lam { ty; _ } -> ty | _ -> assert false

type gen = {
  g_types : cinfo list;
  g_ctors : cinfo list;
  g_recs : cinfo list;
}

(* -------------------------------------------------------------------------- *)
(* add_inductive_fn                                                            *)
(* -------------------------------------------------------------------------- *)
let add_inductive_core env bi pos (overlay : (Name.t, cinfo) Hashtbl.t) (d : decl) (nnested : int) : gen =
  let safety = if d.d_unsafe then Unsafe else Safe in
  (* a fresh checker whenever the overlay has grown, so caches are never stale *)
  let tc () = let c = Tc.create ~local:overlay ~safety env bi pos in c in
  let cur = ref (tc ()) in
  let refresh () = cur := tc () in
  let whnf e = Tc.whnf !cur e in
  let infer e = Tc.infer !cur e in
  let is_def_eq a b = Tc.is_def_eq !cur a b in
  let check e lps = let c = !cur in c.lparams <- Some lps; let r = Tc.check c e in c.lparams <- None; r in
  let ensure_type e = Tc.ensure_sort !cur (infer e) in
  let nparams = d.d_nparams in
  let types = Array.of_list d.d_types in
  let ntypes = Array.length types in
  if ntypes = 0 then fail "empty inductive declaration";
  let levels = List.map Level.param d.d_lparams in
  let ind_consts = Array.map (fun t -> Expr.const t.it_name levels) types in
  let params = Vec.create () in
  let nindices = Array.make ntypes 0 in
  let result_level = ref Level.zero in
  let is_not_zero = ref false in
  (* ---- check_inductive_types ---- *)
  Array.iteri (fun idx t ->
      ignore (check t.it_ty d.d_lparams);
      let ty = ref (whnf t.it_ty) in
      let i = ref 0 in
      while is_pi !ty do
        if !i < nparams then begin
          if idx = 0 then begin
            let p = local_for !ty in
            Vec.push params p;
            ty := instantiate1 (binding_body !ty) p
          end else begin
            if not (is_def_eq (binding_domain !ty) (fvar_ty (Vec.get params !i))) then
              fail "parameters of all inductive datatypes must match";
            ty := instantiate1 (binding_body !ty) (Vec.get params !i)
          end;
          incr i
        end else begin
          let l = local_for !ty in
          ty := instantiate1 (binding_body !ty) l;
          nindices.(idx) <- nindices.(idx) + 1
        end;
        ty := whnf !ty
      done;
      if !i <> nparams then fail "number of parameters mismatch in inductive datatype declaration";
      let s = Tc.ensure_sort !cur !ty in
      if idx = 0 then begin
        result_level := sort_level s;
        is_not_zero := Level.is_not_zero !result_level
      end else if not (Level.is_equiv (sort_level s) !result_level) then
        fail "mutually inductive types must live in the same universe")
    types;
  let params_a = Vec.to_array params in
  let is_ind_occ e = match e with
    | Const { n; _ } -> Array.exists (fun t -> Name.equal t.it_name n) types
    | _ -> false in
  let has_ind_occ t = Expr.exists is_ind_occ t in
  (* ---- declare_inductive_types ---- *)
  let is_rec =
    Array.exists (fun t -> List.exists (fun (_, cty) ->
        let rec go t = match t with
          | Pi { ty; b; _ } -> has_ind_occ ty || go b
          | _ -> false in go cty) t.it_ctors) types in
  let is_reflexive =
    Array.exists (fun t -> List.exists (fun (_, cty) ->
        let rec go t = match t with
          | Pi { ty; _ } ->
            if is_pi ty && has_ind_occ ty then true
            else go (instantiate1 (binding_body t) (local_for t))
          | _ -> false in go cty) t.it_ctors) types in
  let all = Array.to_list (Array.map (fun t -> t.it_name) types) in
  let g_types = Array.to_list (Array.mapi (fun idx t ->
      let ci = { name = t.it_name; lparams = d.d_lparams; ty = t.it_ty; unsafe = d.d_unsafe; pos;
                 kind = Induct { nparams; nindices = nindices.(idx); all; ctors = List.map fst t.it_ctors;
                                 nnested; is_rec; is_reflexive } } in
      Hashtbl.replace overlay t.it_name ci; ci) types) in
  refresh ();
  (* ---- check_constructors ---- *)
  let is_valid_ind_app t idx =
    let fn, args = get_app_args t in
    fn == ind_consts.(idx) && Array.length args = nparams + nindices.(idx) &&
    (let ok = ref true in
     for i = 0 to nparams - 1 do if args.(i) != params_a.(i) then ok := false done;
     for i = nparams to Array.length args - 1 do if has_ind_occ args.(i) then ok := false done;
     !ok) in
  let which_valid_ind_app t =
    let r = ref None in
    for i = ntypes - 1 downto 0 do if is_valid_ind_app t i then r := Some i done; !r in
  let is_rec_argument t =
    let t = ref (whnf t) in
    while is_pi !t do t := whnf (instantiate1 (binding_body !t) (local_for !t)) done;
    which_valid_ind_app !t in
  let rec check_positivity t cname arg_idx =
    let t = whnf t in
    if not (has_ind_occ t) then ()
    else match t with
      | Pi { ty; b; _ } ->
        if has_ind_occ ty then
          fail "arg #%d of '%s' has a non positive occurrence of the datatypes being declared" (arg_idx + 1) (Name.to_string cname);
        check_positivity (instantiate1 b (local_for t)) cname arg_idx
      | _ ->
        if which_valid_ind_app t = None then
          fail "arg #%d of '%s' contains a non valid occurrence of the datatypes being declared" (arg_idx + 1) (Name.to_string cname) in
  Array.iteri (fun idx t ->
      let seen = Hashtbl.create 8 in
      List.iter (fun (n, cty) ->
          if Hashtbl.mem seen n then fail "duplicate constructor name '%s'" (Name.to_string n);
          Hashtbl.add seen n ();
          ignore (check cty d.d_lparams);
          let t = ref cty and i = ref 0 in
          while is_pi !t do
            if !i < nparams then begin
              if not (is_def_eq (binding_domain !t) (fvar_ty params_a.(!i))) then
                fail "arg #%d of '%s' does not match inductive datatypes parameters" (!i + 1) (Name.to_string n);
              t := instantiate1 (binding_body !t) params_a.(!i)
            end else begin
              let s = ensure_type (binding_domain !t) in
              if not (Level.is_geq !result_level (sort_level s) || Level.normalizes_to_zero !result_level) then
                fail "universe level of type_of(arg #%d) of '%s' is too big for the corresponding inductive datatype" (!i + 1) (Name.to_string n);
              if not d.d_unsafe then check_positivity (binding_domain !t) n !i;
              t := instantiate1 (binding_body !t) (local_for !t)
            end;
            incr i
          done;
          if not (is_valid_ind_app !t idx) then fail "invalid return type for '%s'" (Name.to_string n))
        t.it_ctors)
    types;
  (* ---- declare_constructors ---- *)
  let g_ctors = List.concat (Array.to_list (Array.map (fun t ->
      List.mapi (fun cidx (n, cty) ->
          let rec arity t = match t with Pi { b; _ } -> 1 + arity b | _ -> 0 in
          let ar = arity cty in
          if ar < nparams then fail "constructor '%s' has too few arguments" (Name.to_string n);
          let ci = { name = n; lparams = d.d_lparams; ty = cty; unsafe = d.d_unsafe; pos;
                     kind = Ctor { induct = t.it_name; cidx; cnparams = nparams; nfields = ar - nparams } } in
          Hashtbl.replace overlay n ci; ci) t.it_ctors) types)) in
  refresh ();
  (* ---- init_elim_level ---- *)
  let elim_only_at_zero () =
    if !is_not_zero then false
    else if ntypes > 1 then true
    else match types.(0).it_ctors with
      | [] -> false
      | _ :: _ :: _ -> true
      | [(_, cty)] ->
        let ty = ref cty and i = ref 0 in
        let to_check = ref [] in
        while is_pi !ty do
          let fv = local_for !ty in
          if !i >= nparams then begin
            let s = ensure_type (binding_domain !ty) in
            if not (Level.normalizes_to_zero (sort_level s)) then to_check := fv :: !to_check
          end;
          ty := instantiate1 (binding_body !ty) fv;
          incr i
        done;
        let _, result_args = get_app_args !ty in
        List.exists (fun a -> not (Array.exists (fun r -> r == a) result_args)) !to_check in
  let elim_level =
    if elim_only_at_zero () then Level.zero
    else begin
      let u = ref (Name.str Name.Anon "u") and i = ref 1 in
      while List.exists (Name.equal !u) d.d_lparams do
        u := Name.str Name.Anon ("u_" ^ string_of_int !i); incr i
      done;
      Level.param !u
    end in
  (* ---- init_K_target ---- *)
  let k_target =
    ntypes = 1 && Level.normalizes_to_zero !result_level &&
    (match types.(0).it_ctors with
     | [(_, cty)] ->
       let rec ar t = match t with Pi { b; _ } -> 1 + ar b | _ -> 0 in
       ar cty <= nparams
     | _ -> false) in
  (* ---- mk_rec_infos ---- *)
  let get_i_indices t =
    match which_valid_ind_app t with
    | None -> fail "ill-formed inductive application"
    | Some r -> let _, args = get_app_args t in (r, Array.sub args nparams (Array.length args - nparams)) in
  let motives = Array.make ntypes (Lazy.force dontcare) in
  let majors = Array.make ntypes (Lazy.force dontcare) in
  let rindices = Array.make ntypes [||] in
  Array.iteri (fun d_idx t ->
      let ty = ref (whnf t.it_ty) and i = ref 0 in
      let idxs = Vec.create () in
      while is_pi !ty do
        if !i < nparams then ty := instantiate1 (binding_body !ty) params_a.(!i)
        else begin
          let ix = local_for !ty in
          Vec.push idxs ix;
          ty := instantiate1 (binding_body !ty) ix
        end;
        incr i;
        ty := whnf !ty
      done;
      let idxs = Vec.to_array idxs in
      let major = mk_local (mk_app_arr (mk_app_arr ind_consts.(d_idx) params_a) idxs) in
      let c_ty = mk_pi [| major |] (sort elim_level) in
      let c_ty = mk_pi idxs c_ty in
      motives.(d_idx) <- mk_local c_ty;
      majors.(d_idx) <- major;
      rindices.(d_idx) <- idxs) types;
  (* fields of a constructor: returns (b_u, u) *)
  let ctor_fields cty =
    let t = ref cty and i = ref 0 in
    let b_u = Vec.create () and u = Vec.create () in
    while is_pi !t do
      if !i < nparams then t := instantiate1 (binding_body !t) params_a.(!i)
      else begin
        let l = local_for !t in
        Vec.push b_u l;
        if is_rec_argument (binding_domain !t) <> None then Vec.push u l;
        t := instantiate1 (binding_body !t) l
      end;
      incr i
    done;
    (Vec.to_array b_u, Vec.to_array u, !t) in
  (* for a recursive field u_i: its xs and target (type index, indices) *)
  let rec_field_info u_i =
    let ty = ref (whnf (infer u_i)) in
    let xs = Vec.create () in
    while is_pi !ty do
      let x = local_for !ty in
      Vec.push xs x;
      ty := whnf (instantiate1 (binding_body !ty) x)
    done;
    let it_idx, it_indices = get_i_indices !ty in
    (Vec.to_array xs, it_idx, it_indices) in
  let minors = Array.make ntypes [] in
  Array.iteri (fun d_idx t ->
      let ms = List.map (fun (cname, cty) ->
          let b_u, u, rt = ctor_fields cty in
          let it_idx, it_indices = get_i_indices rt in
          let intro_app = mk_app_arr (mk_app_arr (Expr.const cname levels) params_a) b_u in
          let c_app = app (mk_app_arr motives.(it_idx) it_indices) intro_app in
          let v = Array.map (fun u_i ->
              let xs, it_idx, it_indices = rec_field_info u_i in
              let c_app = app (mk_app_arr motives.(it_idx) it_indices) (mk_app_arr u_i xs) in
              mk_local (mk_pi xs c_app)) u in
          mk_local (mk_pi b_u (mk_pi v c_app))) t.it_ctors in
      minors.(d_idx) <- ms) types;
  let rec_levels = (match elim_level with Level.Param _ -> elim_level :: levels | _ -> levels) in
  let rec_lparams = (match elim_level with Level.Param { n; _ } -> n :: d.d_lparams | _ -> d.d_lparams) in
  let all_minors = Array.of_list (List.concat (Array.to_list minors)) in
  let nminors = Array.length all_minors in
  (* ---- declare_recursors ---- *)
  let minor_idx = ref 0 in
  let g_recs = Array.to_list (Array.mapi (fun d_idx t ->
      let c_app = app (mk_app_arr motives.(d_idx) rindices.(d_idx)) majors.(d_idx) in
      let rec_ty = mk_pi [| majors.(d_idx) |] c_app in
      let rec_ty = mk_pi rindices.(d_idx) rec_ty in
      let rec_ty = mk_pi all_minors rec_ty in
      let rec_ty = mk_pi motives rec_ty in
      let rec_ty = mk_pi params_a rec_ty in
      let rules = List.map (fun (cname, cty) ->
          let b_u, u, _ = ctor_fields cty in
          let v = Array.map (fun u_i ->
              let xs, it_idx, it_indices = rec_field_info u_i in
              let rn = rec_name types.(it_idx).it_name in
              let ra = Expr.const rn rec_levels in
              let ra = mk_app_arr (mk_app_arr (mk_app_arr (mk_app_arr ra params_a) motives) all_minors) it_indices in
              mk_lambda xs (app ra (mk_app_arr u_i xs))) u in
          let e_app = mk_app_arr (mk_app_arr all_minors.(!minor_idx) b_u) v in
          let rhs = mk_lambda params_a (mk_lambda motives (mk_lambda all_minors (mk_lambda b_u e_app))) in
          incr minor_idx;
          { r_ctor = cname; r_nfields = Array.length b_u; r_rhs = rhs }) t.it_ctors in
      let rn = rec_name t.it_name in
      let ci = { name = rn; lparams = rec_lparams; ty = rec_ty; unsafe = d.d_unsafe; pos;
                 kind = Recursor { rall = all; rnparams = nparams; rnindices = nindices.(d_idx);
                                   nmotives = ntypes; nminors; rules; k = k_target } } in
      Hashtbl.replace overlay rn ci; ci) types) in
  refresh ();
  (* ---- check_recursors ---- *)
  List.iteri (fun d_idx rci ->
      ignore (check rci.ty rec_lparams);
      let rec_pre = mk_app_arr (mk_app_arr (mk_app_arr (Expr.const rci.name rec_levels) params_a) motives) all_minors in
      List.iter (fun (cname, cty) ->
          let b_u, _, rt = ctor_fields cty in
          let _, it_indices = get_i_indices rt in
          let intro_app = mk_app_arr (mk_app_arr (Expr.const cname levels) params_a) b_u in
          let lhs = app (mk_app_arr rec_pre it_indices) intro_app in
          let c = tc () in
          let expected = Tc.infer c lhs in
          let reduct = Tc.whnf c lhs in
          let actual = Tc.infer c reduct in
          if not (Tc.is_def_eq c actual expected) then
            fail "generated recursor computation rule for '%s' is not type-preserving" (Name.to_string cname))
        types.(d_idx).it_ctors) g_recs;
  { g_types; g_ctors; g_recs }

(* -------------------------------------------------------------------------- *)
(* Nested inductives                                                           *)
(* -------------------------------------------------------------------------- *)
let check_uniform_ind_occs (d : decl) =
  let nparams = d.d_nparams in
  let lvls = List.map Level.param d.d_lparams in
  let is_ind n = List.exists (fun t -> Name.equal t.it_name n) d.d_types in
  let rec go e off = match e with
    | App _ | Const _ ->
      let fn, args = get_app_args e in
      (match fn with
       | Const { n; ls; _ } when is_ind n && Array.length args <= nparams ->
         let ok = ref (Array.length args = nparams && off >= nparams &&
                       List.compare_lengths ls lvls = 0 && List.for_all2 (==) ls lvls) in
         for i = 0 to nparams - 1 do
           if !ok then (match args.(i) with BVar { idx; _ } when idx = off - 1 - i -> () | _ -> ok := false)
         done;
         if not !ok then
           fail "invalid occurrence of datatype '%s' being declared: it must be applied to the parameters and universe levels of the mutual declaration" (Name.to_string n)
       | _ ->
         (match e with
          | App { f; a; _ } -> go f off; go a off
          | _ -> ()))
    | Lam { ty; b; _ } | Pi { ty; b; _ } -> go ty off; go b (off + 1)
    | Let { ty; v; b; _ } -> go ty off; go v off; go b (off + 1)
    | Proj { e; _ } -> go e off
    | _ -> () in
  List.iter (fun t -> List.iter (fun (_, cty) -> go cty 0) t.it_ctors) d.d_types

let check_no_nested_aux e =
  if Expr.exists (fun e -> match e with
      | Const { n; _ } -> Name.is_prefix_of n_nested n
      | Proj { s; _ } -> Name.is_prefix_of n_nested s
      | _ -> false) e
  then fail "invalid declaration, it uses the reserved prefix '_nested'"

type nested_res = {
  nr_params : Expr.t array;
  nr_aux2nested : (Name.t * Expr.t) list;   (* aux type name -> `I Ds` (over nr_params) *)
  nr_decl : decl;
}

let get_params ty nparams =
  let ps = Vec.create () in
  let ty = ref ty in
  for _ = 1 to nparams do
    match !ty with
    | Pi { ty = d; b; _ } -> let p = mk_fvar d in Vec.push ps p; ty := instantiate1 b p
    | _ -> fail "invalid inductive datatype declaration, incorrect number of parameters"
  done;
  (Vec.to_array ps, !ty)

let elim_nested (c : Tc.ctx) (d : decl) : nested_res =
  let lvls = List.map Level.param d.d_lparams in
  let new_types = Vec.create () in
  List.iter (Vec.push new_types) d.d_types;
  let params, _ = get_params (List.hd d.d_types).it_ty d.d_nparams in
  let nested_aux = ref [] in   (* (I Ds over params, auxname) in creation order (reversed) *)
  let next_idx = ref 1 in
  let mk_unique_name n =
    let rec go () =
      let r = Name.append_index_after n !next_idx in
      incr next_idx;
      if Tc.find c r <> None then go () else r in
    go () in
  let replace_params e as_ = instantiate_rev (abstract e as_ (Array.length as_)) params in
  let instantiate_pi_params e np args =
    let e = ref e in
    for _ = 1 to np do
      match !e with Pi { b; _ } -> e := b | _ -> fail "invalid nested inductive datatype, ill-formed declaration"
    done;
    instantiate_rev_sub !e args np in
  let is_new n = let r = ref false in
    for i = 0 to Vec.length new_types - 1 do if Name.equal (Vec.get new_types i).it_name n then r := true done; !r in
  let is_nested_app e =
    match e with
    | App _ ->
      let fn, args = get_app_args e in
      (match fn with
       | Const { n; _ } ->
         (match Tc.find c n with
          | Some { kind = Induct iv; _ } ->
            if iv.nparams > Array.length args then None else begin
              let is_nested = ref false and loose = ref false in
              for i = 0 to iv.nparams - 1 do
                if not (closed args.(i)) then loose := true;
                if Expr.exists (fun t -> match t with Const { n; _ } -> is_new n | _ -> false) args.(i) then is_nested := true
              done;
              if not !is_nested then None
              else if !loose then
                fail "invalid nested inductive datatype '%s', nested inductive datatypes parameters cannot contain local variables." (Name.to_string n)
              else Some iv
            end
          | _ -> None)
       | _ -> None)
    | _ -> None in
  let replace_if_nested as_ e =
    match is_nested_app e with
    | None -> None
    | Some iv ->
      let fn, args = get_app_args e in
      let i_name, i_lvls = match fn with Const { n; ls; _ } -> n, ls | _ -> assert false in
      let inp = iv.nparams in
      let ias = mk_app_sub fn args 0 inp in
      let iparams = replace_params ias as_ in
      let found = List.find_opt (fun (p, _) -> p == iparams) !nested_aux in
      (match found with
       | Some (_, auxn) ->
         let auxi = mk_app_arr (Expr.const auxn lvls) as_ in
         Some (mk_app_sub auxi args inp (Array.length args))
       | None ->
         let result = ref None in
         List.iter (fun j_name ->
             let j_info = Tc.get c j_name in
             let j_ctors = match j_info.kind with Induct jv -> jv.ctors | _ -> fail "ill-formed nested inductive" in
             let jas = mk_app_sub (Expr.const j_name i_lvls) args 0 inp in
             let auxj_name = mk_unique_name (Name.append n_nested j_name) in
             let auxj_type = instantiate_lparams j_info.ty j_info.lparams i_lvls in
             let auxj_type = instantiate_pi_params auxj_type inp args in
             let auxj_type = mk_pi as_ auxj_type in
             nested_aux := !nested_aux @ [ (replace_params jas as_, auxj_name) ];
             if Name.equal j_name i_name then begin
               let auxi = mk_app_arr (Expr.const auxj_name lvls) as_ in
               result := Some (mk_app_sub auxi args inp (Array.length args))
             end;
             let ctors = List.map (fun jc ->
                 let jci = Tc.get c jc in
                 let n = Name.replace_prefix jc j_name auxj_name in
                 let t = instantiate_lparams jci.ty jci.lparams i_lvls in
                 let t = instantiate_pi_params t inp args in
                 (n, mk_pi as_ t)) j_ctors in
             Vec.push new_types { it_name = auxj_name; it_ty = auxj_type; it_ctors = ctors })
           iv.all;
         (match !result with Some r -> Some r | None -> fail "ill-formed nested inductive"))
  in
  let qhead = ref 0 in
  while !qhead < Vec.length new_types do
    let t = Vec.get new_types !qhead in
    let ctors = List.map (fun (n, cty) ->
        let as_, body = get_params cty d.d_nparams in
        let nb = Expr.replace (replace_if_nested as_) body in
        (n, mk_pi as_ nb)) t.it_ctors in
    (Vec.data new_types).(!qhead) <- { t with it_ctors = ctors };
    incr qhead
  done;
  { nr_params = params;
    nr_aux2nested = List.map (fun (e, n) -> (n, e)) !nested_aux;
    nr_decl = { d with d_types = Array.to_list (Vec.to_array new_types) } }

(* -------------------------------------------------------------------------- *)
(* Entry point                                                                 *)
(* -------------------------------------------------------------------------- *)
let add_inductive env bi pos (d : decl) : gen =
  List.iter (fun t ->
      check_no_nested_aux t.it_ty;
      List.iter (fun (_, cty) -> check_no_nested_aux cty) t.it_ctors) d.d_types;
  (* duplicated universe parameters *)
  let rec dup = function [] -> false | x :: r -> List.exists (Name.equal x) r || dup r in
  if dup d.d_lparams then fail "duplicate universe level parameter";
  check_uniform_ind_occs d;
  let c0 = Tc.create env bi pos in
  let res = elim_nested c0 d in
  let nnested = List.length res.nr_aux2nested in
  let aux_overlay = Hashtbl.create 64 in
  let aux = add_inductive_core env bi pos aux_overlay res.nr_decl nnested in
  if nnested = 0 then aux
  else begin
    let ntypes = List.length d.d_types in
    let all_names = List.map (fun t -> t.it_name) d.d_types in
    let main_name = (List.hd d.d_types).it_name in
    (* aux recursor renaming *)
    let aux_rec_map =
      List.mapi (fun i t -> (rec_name t.it_name, Name.append_index_after (rec_name main_name) (i + 1)))
        (List.filteri (fun i _ -> i >= ntypes) res.nr_decl.d_types) in
    let aux_types = List.filteri (fun i _ -> i >= ntypes) res.nr_decl.d_types in
    let aux_ctor_owner = Hashtbl.create 16 in
    List.iter (fun t -> List.iter (fun (cn, _) -> Hashtbl.replace aux_ctor_owner cn t.it_name) t.it_ctors) aux_types;
    let np = Array.length res.nr_params in
    let restore_ctor_name cn =
      match Hashtbl.find_opt aux_ctor_owner cn with
      | None -> fail "failed to restore nested inductive types"
      | Some auxi ->
        let nested = List.assoc auxi res.nr_aux2nested in
        (match get_app_fn nested with
         | Const { n; _ } -> Name.replace_prefix cn auxi n
         | _ -> fail "failed to restore nested inductive types") in
    let restore_nested e =
      let as_ = Vec.create () in
      let is_pi0 = is_pi e in
      let e = ref e in
      for _ = 1 to np do
        match !e with
        | Pi { ty; b; _ } | Lam { ty; b; _ } -> let a = mk_fvar ty in Vec.push as_ a; e := instantiate1 b a
        | _ -> fail "failed to restore nested inductive types, fewer binders than parameters"
      done;
      let as_ = Vec.to_array as_ in
      let f t =
        match t with
        | Const { n; ls; _ } when List.exists (fun (a, _) -> Name.equal a n) aux_rec_map ->
          Some (Expr.const (List.assoc n aux_rec_map) ls)
        | _ ->
          match get_app_fn t with
          | Const { n; _ } ->
            (match List.find_opt (fun (a, _) -> Name.equal a n) res.nr_aux2nested with
             | Some (_, nested) ->
               let _, args = get_app_args t in
               if Array.length args < np then fail "failed to restore nested inductive types";
               let nt = instantiate_rev (abstract nested res.nr_params np) as_ in
               Some (mk_app_sub nt args np (Array.length args))
             | None ->
               match Hashtbl.find_opt aux_ctor_owner n with
               | Some auxi ->
                 let nested = List.assoc auxi res.nr_aux2nested in
                 let _, args = get_app_args t in
                 if Array.length args < np then fail "failed to restore nested inductive types";
                 let new_nested = instantiate_rev (abstract nested res.nr_params np) as_ in
                 let i, i_args = get_app_args new_nested in
                 (match i with
                  | Const { n = iname; ls = ils; _ } ->
                    let new_fn = Expr.const (Name.replace_prefix n auxi iname) ils in
                    Some (mk_app_sub (mk_app_arr new_fn i_args) args np (Array.length args))
                  | _ -> fail "failed to restore nested inductive types")
               | None -> None)
          | _ -> None in
      let e' = Expr.replace f !e in
      if is_pi0 then mk_pi as_ e' else mk_lambda as_ e' in
    let g_types = List.filteri (fun i _ -> i < ntypes) aux.g_types
                  |> List.map (fun ci -> match ci.kind with
                      | Induct iv -> { ci with kind = Induct { iv with all = all_names } }
                      | _ -> assert false) in
    let orig_ctor_names = List.concat_map (fun t -> List.map fst t.it_ctors) d.d_types in
    let g_ctors = List.filter (fun ci -> List.exists (Name.equal ci.name) orig_ctor_names) aux.g_ctors
                  |> List.map (fun ci -> { ci with ty = restore_nested ci.ty }) in
    let g_recs = List.map (fun ci ->
        let renamed = List.assoc_opt ci.name (List.map (fun (a, b) -> (a, b)) aux_rec_map) in
        let new_name = match renamed with Some n -> n | None -> ci.name in
        match ci.kind with
        | Recursor r ->
          let rules = List.map (fun rl ->
              { r_ctor = (if renamed <> None then restore_ctor_name rl.r_ctor else rl.r_ctor);
                r_nfields = rl.r_nfields; r_rhs = restore_nested rl.r_rhs }) r.rules in
          { ci with name = new_name; ty = restore_nested ci.ty;
                    kind = Recursor { r with rall = all_names; rules } }
        | _ -> assert false) aux.g_recs in
    (* type check the nested occurrences and re-check the restored terms in the
       real (restored) environment *)
    let overlay = Hashtbl.create 64 in
    List.iter (fun ci -> Hashtbl.replace overlay ci.name ci) (g_types @ g_ctors @ g_recs);
    let safety = if d.d_unsafe then Unsafe else Safe in
    let c = Tc.create ~local:overlay ~safety env bi pos in
    c.lparams <- Some d.d_lparams;
    List.iter (fun (_, nested) -> ignore (Tc.check c nested)) res.nr_aux2nested;
    List.iter (fun ci -> ignore (Tc.check c ci.ty)) g_ctors;
    List.iter (fun (ci : cinfo) ->
        c.lparams <- Some ci.lparams;
        ignore (Tc.check c ci.ty);
        match ci.kind with
        | Recursor r -> List.iter (fun rl -> ignore (Tc.check c rl.r_rhs)) r.rules
        | _ -> ()) g_recs;
    { g_types; g_ctors; g_recs }
  end
