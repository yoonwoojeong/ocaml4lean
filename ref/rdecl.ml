(* Declarations for the reference checker: axioms, definitions, theorems,
   opaque constants, the quotient package, and inductive types.

   An inductive block is not trusted at all: the inductive types, constructors
   and recursors (with their computation rules) are re-derived from the types
   and constructor types alone, following Lean's kernel/inductive.cpp, and every
   exported member must equal the derived one.  Nested inductives are first
   translated to mutual ones with auxiliary types, and translated back. *)
open Rterm
open Rtc

(* ------------------------------------------------------------ helpers *)
let rec dup_free = function [] -> true | x :: r -> not (List.mem x r) && dup_free r

let rec arity = function Pi (_, b) -> 1 + arity b | _ -> 0

(* replace: f is tried on every node first; Some r replaces the node without
   descending into it *)
let rec replace (f : term -> term option) (t : term) : term =
  match f t with
  | Some r -> r
  | None ->
    match t with
    | App (a, b) -> App (replace f a, replace f b)
    | Lam (a, b) -> Lam (replace f a, replace f b)
    | Pi (a, b) -> Pi (replace f a, replace f b)
    | Let (a, b, c) -> Let (replace f a, replace f b, replace f c)
    | Proj (s, i, e) -> Proj (s, i, replace f e)
    | _ -> t

let optParam = n_ "optParam" and autoParam = n_ "autoParam"
let outParam = n_ "outParam" and semiOutParam = n_ "semiOutParam"
let rec consume t =
  match app_fn t, app_args t with
  | Const (n, _), [a; _] when n = optParam || n = autoParam -> consume a
  | Const (n, _), [a] when n = outParam || n = semiOutParam -> consume a
  | _ -> t

let local_for = function
  | Pi (d, _) | Lam (d, _) -> fresh_fvar (consume d)
  | _ -> invalid_arg "local_for"
let body_of = function Pi (_, b) | Lam (_, b) -> b | _ -> invalid_arg "body_of"
let dom_of = function Pi (d, _) | Lam (d, _) -> d | _ -> invalid_arg "dom_of"
let is_pi = function Pi _ -> true | _ -> false

(* check a term in the context of the given universe parameters *)
let with_lps lps safety f =
  set_context (Some lps) safety;
  let r = (try f () with e -> set_context None Safe; raise e) in
  set_context None Safe; r

(* ----------------------------------------------------- inductive input *)
type ind_type = { it_name : name; it_ty : term; it_ctors : (name * term) list }
type ind_decl = { d_lparams : name list; d_nparams : int; d_types : ind_type list; d_unsafe : bool }

let rec_name n = n @ [S "rec"]

(* result of the core algorithm: declarations in the order types, ctors, recs *)
type derived = { g_types : decl list; g_ctors : decl list; g_recs : decl list }

let rec add_inductive_core (d : ind_decl) (nnested : int) : derived =
  let safety = if d.d_unsafe then Unsafe else Safe in
  set_context (Some d.d_lparams) safety;
  match core_body d nnested safety with
  | r -> set_context None Safe; r
  | exception e -> set_context None Safe; raise e

and core_body (d : ind_decl) (nnested : int) safety : derived =
  let nparams = d.d_nparams in
  let types = Array.of_list d.d_types in
  let ntypes = Array.length types in
  if ntypes = 0 then fail "empty inductive declaration";
  let levels = List.map (fun n -> Param n) d.d_lparams in
  let ind_consts = Array.map (fun t -> Const (t.it_name, levels)) types in
  let ctx f = f () in
  (* ---- the inductive types ---- *)
  let params = ref [] in             (* parameter locals, from the first type *)
  let nindices = Array.make ntypes 0 in
  let result_level = ref Zero in
  Array.iteri (fun idx t ->
      ctx (fun () -> ignore (ensure_sort (infer t.it_ty)));
      let ty = ref (whnf t.it_ty) in
      let i = ref 0 in
      while is_pi !ty do
        if !i < nparams then begin
          if idx = 0 then begin
            let p = local_for !ty in
            params := !params @ [p];
            ty := instantiate1 (body_of !ty) p
          end else begin
            let p = List.nth !params !i in
            if not (is_def_eq (dom_of !ty) (match p with Fvar id -> fvar_type id | _ -> assert false)) then
              fail "parameters of all inductive datatypes must match";
            ty := instantiate1 (body_of !ty) p
          end;
          incr i
        end else begin
          let l = local_for !ty in
          ty := instantiate1 (body_of !ty) l;
          nindices.(idx) <- nindices.(idx) + 1
        end;
        ty := whnf !ty
      done;
      if !i <> nparams then fail "number of parameters mismatch in inductive datatype declaration";
      let lvl = ensure_sort !ty in
      if idx = 0 then result_level := lvl
      else if not (level_equiv lvl !result_level) then fail "mutually inductive types must live in the same universe")
    types;
  let params_a = !params in
  let is_not_zero = level_never_zero !result_level in
  let is_ind_occ = function Const (n, _) -> Array.exists (fun t -> t.it_name = n) types | _ -> false in
  let has_ind_occ t = exists is_ind_occ t in
  let all = Array.to_list (Array.map (fun t -> t.it_name) types) in
  let is_rec =
    Array.exists (fun t -> List.exists (fun (_, cty) ->
        let rec go = function Pi (a, b) -> has_ind_occ a || go b | _ -> false in go cty) t.it_ctors) types in
  let is_reflexive =
    Array.exists (fun t -> List.exists (fun (_, cty) ->
        let rec go t = match t with
          | Pi (a, _) -> (is_pi a && has_ind_occ a) || go (instantiate1 (body_of t) (local_for t))
          | _ -> false in go cty) t.it_ctors) types in
  let g_types = Array.to_list (Array.mapi (fun idx t ->
      { name = t.it_name; lparams = d.d_lparams; ty = t.it_ty; unsafe = d.d_unsafe;
        kind = Induct { nparams; nindices = nindices.(idx); all; ctors = List.map fst t.it_ctors;
                        nnested; is_rec; is_reflexive } }) types) in
  List.iter add_decl g_types;
  (* ---- the constructors ---- *)
  let is_valid_ind_app t idx =
    let args = app_args t in
    app_fn t = ind_consts.(idx) && List.length args = nparams + nindices.(idx)
    && (let ok = ref true in
        List.iteri (fun i a -> if i < nparams && a <> List.nth params_a i then ok := false) args; !ok) in
  let which_valid_ind_app t =
    let r = ref None in
    for i = ntypes - 1 downto 0 do if is_valid_ind_app t i then r := Some i done; !r in
  let is_rec_argument t =
    let t = ref (whnf t) in
    while is_pi !t do t := whnf (instantiate1 (body_of !t) (local_for !t)) done;
    which_valid_ind_app !t in
  let rec check_positivity t cname arg_idx =
    let t = whnf t in
    if not (has_ind_occ t) then ()
    else match t with
      | Pi (a, _) ->
        if has_ind_occ a then
          fail "arg #%d of '%s' has a non positive occurrence of the datatypes being declared" (arg_idx + 1) (name_to_string cname);
        check_positivity (instantiate1 (body_of t) (local_for t)) cname arg_idx
      | _ ->
        if which_valid_ind_app t = None then
          fail "arg #%d of '%s' contains a non valid occurrence of the datatypes being declared" (arg_idx + 1) (name_to_string cname) in
  Array.iteri (fun idx t ->
      let seen = ref [] in
      List.iter (fun (cn, cty) ->
          if List.mem cn !seen then fail "duplicate constructor name '%s'" (name_to_string cn);
          seen := cn :: !seen;
          if find cn <> None then fail "constructor '%s' is already declared" (name_to_string cn);
          ctx (fun () -> ignore (infer cty));
          let t = ref cty and i = ref 0 in
          while is_pi !t do
            if !i < nparams then begin
              let p = List.nth params_a !i in
              if not (is_def_eq (dom_of !t) (match p with Fvar id -> fvar_type id | _ -> assert false)) then
                fail "arg #%d of '%s' does not match inductive datatypes parameters" (!i + 1) (name_to_string cn);
              t := instantiate1 (body_of !t) p
            end else begin
              let lvl = ensure_sort (infer (dom_of !t)) in
              if not (level_geq !result_level lvl || level_is_zero !result_level) then
                fail "universe level of type_of(arg #%d) of '%s' is too big for the corresponding inductive datatype" (!i + 1) (name_to_string cn);
              if not d.d_unsafe then check_positivity (dom_of !t) cn !i;
              t := instantiate1 (body_of !t) (local_for !t)
            end;
            incr i
          done;
          if not (is_valid_ind_app !t idx) then fail "invalid return type for '%s'" (name_to_string cn))
        t.it_ctors)
    types;
  let g_ctors = List.concat (Array.to_list (Array.map (fun t ->
      List.mapi (fun cidx (cn, cty) ->
          let ar = arity cty in
          if ar < nparams then fail "constructor '%s' has too few arguments" (name_to_string cn);
          { name = cn; lparams = d.d_lparams; ty = cty; unsafe = d.d_unsafe;
            kind = Ctor { induct = t.it_name; cidx; cnparams = nparams; nfields = ar - nparams } }) t.it_ctors) types)) in
  List.iter add_decl g_ctors;
  (* ---- the eliminator universe ---- *)
  let elim_only_at_zero () =
    if is_not_zero then false
    else if ntypes > 1 then true
    else match types.(0).it_ctors with
      | [] -> false
      | _ :: _ :: _ -> true
      | [(_, cty)] ->
        let ty = ref cty and i = ref 0 and to_check = ref [] in
        while is_pi !ty do
          let fv = local_for !ty in
          if !i >= nparams then begin
            let lvl = ctx (fun () -> ensure_sort (infer (dom_of !ty))) in
            if not (level_is_zero lvl) then to_check := fv :: !to_check
          end;
          ty := instantiate1 (body_of !ty) fv;
          incr i
        done;
        let result_args = app_args !ty in
        List.exists (fun a -> not (List.mem a result_args)) !to_check in
  let elim_level =
    if elim_only_at_zero () then Zero
    else begin
      let u = ref [S "u"] and i = ref 1 in
      while List.mem !u d.d_lparams do u := [S ("u_" ^ string_of_int !i)]; incr i done;
      Param !u
    end in
  let k_target =
    ntypes = 1 && level_is_zero !result_level
    && (match types.(0).it_ctors with [(_, cty)] -> arity cty <= nparams | _ -> false) in
  (* ---- motives, majors, minors ---- *)
  let get_i_indices t =
    match which_valid_ind_app t with
    | None -> fail "ill-formed inductive application"
    | Some r -> (r, List.filteri (fun i _ -> i >= nparams) (app_args t)) in
  let motives = Array.make ntypes prop and majors = Array.make ntypes prop in
  let rindices = Array.make ntypes [] in
  Array.iteri (fun d_idx t ->
      let ty = ref (whnf t.it_ty) and i = ref 0 and idxs = ref [] in
      while is_pi !ty do
        if !i < nparams then ty := instantiate1 (body_of !ty) (List.nth params_a !i)
        else begin
          let ix = local_for !ty in
          idxs := !idxs @ [ix];
          ty := instantiate1 (body_of !ty) ix
        end;
        incr i;
        ty := whnf !ty
      done;
      let major = fresh_fvar (mk_app (mk_app ind_consts.(d_idx) params_a) !idxs) in
      majors.(d_idx) <- major;
      rindices.(d_idx) <- !idxs;
      motives.(d_idx) <- fresh_fvar (mk_pi !idxs (mk_pi [major] (Sort elim_level)))) types;
  let motives_l = Array.to_list motives in
  (* the fields of a constructor: all fields, the recursive ones, the result type *)
  let ctor_fields cty =
    let t = ref cty and i = ref 0 and b_u = ref [] and u = ref [] in
    while is_pi !t do
      if !i < nparams then t := instantiate1 (body_of !t) (List.nth params_a !i)
      else begin
        let l = local_for !t in
        b_u := !b_u @ [l];
        if is_rec_argument (dom_of !t) <> None then u := !u @ [l];
        t := instantiate1 (body_of !t) l
      end;
      incr i
    done;
    (!b_u, !u, !t) in
  let rec_field_info u_i =
    let ty = ref (whnf (infer u_i)) and xs = ref [] in
    while is_pi !ty do
      let x = local_for !ty in
      xs := !xs @ [x];
      ty := whnf (instantiate1 (body_of !ty) x)
    done;
    let it_idx, it_indices = get_i_indices !ty in
    (!xs, it_idx, it_indices) in
  let minors = Array.make ntypes [] in
  Array.iteri (fun d_idx t ->
      minors.(d_idx) <- List.map (fun (cname, cty) ->
          let b_u, u, rt = ctor_fields cty in
          let it_idx, it_indices = get_i_indices rt in
          let intro_app = mk_app (mk_app (Const (cname, levels)) params_a) b_u in
          let c_app = App (mk_app motives.(it_idx) it_indices, intro_app) in
          let v = List.map (fun u_i ->
              let xs, it_idx, it_indices = rec_field_info u_i in
              let c_app = App (mk_app motives.(it_idx) it_indices, mk_app u_i xs) in
              fresh_fvar (mk_pi xs c_app)) u in
          fresh_fvar (mk_pi b_u (mk_pi v c_app))) t.it_ctors) types;
  let rec_levels = (match elim_level with Param _ -> elim_level :: levels | _ -> levels) in
  let rec_lparams = (match elim_level with Param n -> n :: d.d_lparams | _ -> d.d_lparams) in
  let all_minors = List.concat (Array.to_list minors) in
  let nminors = List.length all_minors in
  (* ---- the recursors ---- *)
  let minor_idx = ref 0 in
  let g_recs = Array.to_list (Array.mapi (fun d_idx t ->
      let c_app = App (mk_app motives.(d_idx) rindices.(d_idx), majors.(d_idx)) in
      let rec_ty = mk_pi (params_a @ motives_l @ all_minors @ rindices.(d_idx) @ [majors.(d_idx)]) c_app in
      let rules = List.map (fun (cname, cty) ->
          let b_u, u, _ = ctor_fields cty in
          let v = List.map (fun u_i ->
              let xs, it_idx, it_indices = rec_field_info u_i in
              let ra = Const (rec_name types.(it_idx).it_name, rec_levels) in
              let ra = mk_app (mk_app (mk_app (mk_app ra params_a) motives_l) all_minors) it_indices in
              mk_lam xs (App (ra, mk_app u_i xs))) u in
          let e_app = mk_app (mk_app (List.nth all_minors !minor_idx) b_u) v in
          let rhs = mk_lam (params_a @ motives_l @ all_minors @ b_u) e_app in
          incr minor_idx;
          { r_ctor = cname; r_nfields = List.length b_u; r_rhs = rhs }) t.it_ctors in
      { name = rec_name t.it_name; lparams = rec_lparams; ty = rec_ty; unsafe = d.d_unsafe;
        kind = Rec { rall = all; rnparams = nparams; rnindices = nindices.(d_idx); nmotives = ntypes;
                     nminors; rules; k = k_target } }) types) in
  List.iter add_decl g_recs;
  (* sanity: the derived recursor types are well typed *)
  List.iter (fun (r : decl) -> with_lps r.lparams safety (fun () -> ignore (infer r.ty))) g_recs;
  { g_types; g_ctors; g_recs }

(* ------------------------------------------------------ nested inductives *)
let n_nested = [S "_nested"]
let is_prefix p n =
  let rec go p n = match p, n with [], _ -> true | x :: pr, y :: nr -> x = y && go pr nr | _ -> false in go p n
let replace_prefix n old nw =
  if is_prefix old n then nw @ List.filteri (fun i _ -> i >= List.length old) n else n
let append_index_after n i = (* Name.appendIndexAfter: last string component gets "_i" *)
  match List.rev n with
  | S s :: r -> List.rev (S (s ^ "_" ^ string_of_int i) :: r)
  | r -> List.rev (S ("_" ^ string_of_int i) :: r)

type nested_res = {
  nr_params : term list;
  nr_aux : (name * term) list;       (* aux type name -> the nested application `I Ds` over nr_params *)
  nr_decl : ind_decl;
}

let get_params ty np =
  let ps = ref [] and ty = ref ty in
  for _ = 1 to np do
    match !ty with
    | Pi (d, b) -> let p = fresh_fvar d in ps := !ps @ [p]; ty := instantiate1 b p
    | _ -> fail "invalid inductive datatype declaration, incorrect number of parameters"
  done;
  (!ps, !ty)

let abstract_all (xs : term list) (t : term) : term = (* closed t over xs -> body with loose bvars 0..n-1 *)
  (* x_j (0-based, outermost first) becomes Bvar (n-1-j) *)
  let n = List.length xs in
  List.fold_left (fun (t, j) x ->
      match x with Fvar id -> (abstract_fvar id (n - 1 - j) t, j + 1) | _ -> assert false) (t, 0) xs |> fst

(* instantiate loose bvars 0..n-1 (outermost = n-1) of body with ys (closed terms) *)
let instantiate_all (ys : term list) (body : term) : term =
  let n = List.length ys in
  let rec go b = function
    | [] -> b
    | y :: rest -> go (subst 0 y b) rest in
  ignore n;
  go body (List.rev ys)

let elim_nested (d : ind_decl) : nested_res =
  let lvls = List.map (fun n -> Param n) d.d_lparams in
  let new_types = ref d.d_types in
  let params, _ = get_params (List.hd d.d_types).it_ty d.d_nparams in
  let nested_aux = ref [] in                      (* (I Ds over params, aux name) *)
  let next_idx = ref 1 in
  let mk_unique_name n =
    let rec go () =
      let r = append_index_after n !next_idx in
      incr next_idx;
      if find r <> None then go () else r in
    go () in
  let replace_params e as_ = instantiate_all params (abstract_all as_ e) in
  let instantiate_pi_params e np args =
    let e = ref e in
    for _ = 1 to np do
      match !e with Pi (_, b) -> e := b | _ -> fail "invalid nested inductive datatype, ill-formed declaration"
    done;
    instantiate_all (List.filteri (fun i _ -> i < np) args) !e in
  let is_new n = List.exists (fun t -> t.it_name = n) !new_types in
  let is_nested_app e =
    match e with
    | App _ ->
      (match app_fn e with
       | Const (n, _) ->
         (match find n with
          | Some { kind = Induct iv; _ } ->
            let args = app_args e in
            if iv.nparams > List.length args then None
            else begin
              let is_nested = ref false and loose = ref false in
              List.iteri (fun i a ->
                  if i < iv.nparams then begin
                    if has_loose 0 a then loose := true;
                    if exists (function Const (m, _) -> is_new m | _ -> false) a then is_nested := true
                  end) args;
              if not !is_nested then None
              else if !loose then
                fail "invalid nested inductive datatype '%s', nested inductive datatypes parameters cannot contain local variables." (name_to_string n)
              else Some iv
            end
          | _ -> None)
       | _ -> None)
    | _ -> None in
  let replace_if_nested as_ e =
    match is_nested_app e with
    | None -> None
    | Some iv ->
      let i_name, i_lvls = (match app_fn e with Const (n, ls) -> n, ls | _ -> assert false) in
      let args = app_args e in
      let inp = iv.nparams in
      let first = List.filteri (fun i _ -> i < inp) args and rest = List.filteri (fun i _ -> i >= inp) args in
      let ias = mk_app (app_fn e) first in
      let iparams = replace_params ias as_ in
      (match List.find_opt (fun (p, _) -> p = iparams) !nested_aux with
       | Some (_, auxn) -> Some (mk_app (mk_app (Const (auxn, lvls)) as_) rest)
       | None ->
         let result = ref None in
         List.iter (fun j_name ->
             let j_info = get j_name in
             let j_ctors = (match j_info.kind with Induct jv -> jv.ctors | _ -> fail "ill-formed nested inductive") in
             let jas = mk_app (Const (j_name, i_lvls)) first in
             let auxj_name = mk_unique_name (n_nested @ j_name) in
             let auxj_type = subst_levels j_info.lparams i_lvls j_info.ty in
             let auxj_type = mk_pi as_ (instantiate_pi_params auxj_type inp first) in
             nested_aux := !nested_aux @ [ (replace_params jas as_, auxj_name) ];
             if j_name = i_name then result := Some (mk_app (mk_app (Const (auxj_name, lvls)) as_) rest);
             let ctors = List.map (fun jc ->
                 let jci = get jc in
                 let t = subst_levels jci.lparams i_lvls jci.ty in
                 (replace_prefix jc j_name auxj_name, mk_pi as_ (instantiate_pi_params t inp first))) j_ctors in
             new_types := !new_types @ [ { it_name = auxj_name; it_ty = auxj_type; it_ctors = ctors } ])
           iv.all;
         (match !result with Some r -> Some r | None -> fail "ill-formed nested inductive")) in
  let qhead = ref 0 in
  while !qhead < List.length !new_types do
    let t = List.nth !new_types !qhead in
    let ctors = List.map (fun (cn, cty) ->
        let as_, body = get_params cty d.d_nparams in
        let nb = replace (replace_if_nested as_) body in
        (cn, mk_pi as_ nb)) t.it_ctors in
    new_types := List.mapi (fun i x -> if i = !qhead then { t with it_ctors = ctors } else x) !new_types;
    incr qhead
  done;
  { nr_params = params; nr_aux = List.map (fun (e, n) -> (n, e)) !nested_aux;
    nr_decl = { d with d_types = !new_types } }

(* ---------------------------------------------------- comparing results *)
let rename_lparams (g : decl) (target : name list) : decl =
  if g.lparams = target || List.length g.lparams <> List.length target || not (dup_free target) then g
  else begin
    let ls = List.map (fun n -> Param n) target in
    let inst e = subst_levels g.lparams ls e in
    let kind = match g.kind with
      | Rec r -> Rec { r with rules = List.map (fun rl -> { rl with r_rhs = inst rl.r_rhs }) r.rules }
      | k -> k in
    { g with lparams = target; ty = inst g.ty; kind }
  end

let kind_equal a b = match a, b with
  | Induct x, Induct y ->
    x.nparams = y.nparams && x.nindices = y.nindices && x.all = y.all && x.ctors = y.ctors
    && x.nnested = y.nnested && x.is_rec = y.is_rec && x.is_reflexive = y.is_reflexive
  | Ctor x, Ctor y -> x = y
  | Rec x, Rec y ->
    x.rall = y.rall && x.rnparams = y.rnparams && x.rnindices = y.rnindices && x.nmotives = y.nmotives
    && x.nminors = y.nminors && x.k = y.k && List.length x.rules = List.length y.rules
    && List.for_all2 (fun r s -> r.r_ctor = s.r_ctor && r.r_nfields = s.r_nfields && term_eq r.r_rhs s.r_rhs) x.rules y.rules
  | _ -> false

let same_decl what (g : decl) (e : decl) =
  let g = rename_lparams g e.lparams in
  if not (g.name = e.name && g.lparams = e.lparams && g.unsafe = e.unsafe) then
    fail "exported %s '%s' does not match the derived one (name, universe parameters or safety)" what (name_to_string e.name);
  if not (term_eq g.ty e.ty) then fail "exported %s '%s' has a type different from the derived one" what (name_to_string e.name);
  if not (kind_equal g.kind e.kind) then fail "exported %s '%s' differs from the derived one" what (name_to_string e.name)

(* ------------------------------------------------------------ entry point *)
let add_inductive (d : ind_decl) : derived =
  List.iter (fun t ->
      let bad = exists (function Const (n, _) -> is_prefix n_nested n | Proj (s, _, _) -> is_prefix n_nested s | _ -> false) in
      if bad t.it_ty || List.exists (fun (_, c) -> bad c) t.it_ctors then fail "invalid declaration, it uses the reserved prefix '_nested'";
      if find t.it_name <> None then fail "'%s' is already declared" (name_to_string t.it_name)) d.d_types;
  if not (dup_free d.d_lparams) then fail "duplicate universe level parameter";
  let res = elim_nested d in
  let nnested = List.length res.nr_aux in
  let before = if nnested = 0 then Hashtbl.create 1 else Hashtbl.copy env in
  let aux = add_inductive_core res.nr_decl nnested in
  if nnested = 0 then aux
  else begin
    let ntypes = List.length d.d_types in
    let all_names = List.map (fun t -> t.it_name) d.d_types in
    let main_name = (List.hd d.d_types).it_name in
    let np = List.length res.nr_params in
    let aux_types = List.filteri (fun i _ -> i >= ntypes) res.nr_decl.d_types in
    let aux_rec_map = List.mapi (fun i t -> (rec_name t.it_name, append_index_after (rec_name main_name) (i + 1))) aux_types in
    let aux_ctor_owner = List.concat_map (fun t -> List.map (fun (cn, _) -> (cn, t.it_name)) t.it_ctors) aux_types in
    let nested_of auxi = List.assoc auxi res.nr_aux in
    let restore_ctor_name cn =
      match List.assoc_opt cn aux_ctor_owner with
      | None -> fail "failed to restore nested inductive types"
      | Some auxi -> (match app_fn (nested_of auxi) with
          | Const (n, _) -> replace_prefix cn auxi n
          | _ -> fail "failed to restore nested inductive types") in
    (* open the leading np binders as locals, replace, and close again *)
    let restore_nested e =
      let is_pi0 = is_pi e in
      let as_ = ref [] and cur = ref e in
      for _ = 1 to np do
        match !cur with
        | Pi (t, b) | Lam (t, b) -> let a = fresh_fvar t in as_ := !as_ @ [a]; cur := instantiate1 b a
        | _ -> fail "failed to restore nested inductive types, fewer binders than parameters"
      done;
      let as_ = !as_ in
      let f t =
        match t with
        | Const (n, ls) when List.mem_assoc n aux_rec_map -> Some (Const (List.assoc n aux_rec_map, ls))
        | _ ->
          match app_fn t with
          | Const (n, _) ->
            let args = app_args t in
            let first = List.filteri (fun i _ -> i < np) args and rest = List.filteri (fun i _ -> i >= np) args in
            (match List.assoc_opt n res.nr_aux with
             | Some nested ->
               if List.length args < np then fail "failed to restore nested inductive types";
               let nt = instantiate_all first (abstract_all res.nr_params nested) in
               Some (mk_app nt rest)
             | None ->
               match List.assoc_opt n aux_ctor_owner with
               | Some auxi ->
                 if List.length args < np then fail "failed to restore nested inductive types";
                 let nested = nested_of auxi in
                 let new_nested = instantiate_all first (abstract_all res.nr_params nested) in
                 (match app_fn new_nested with
                  | Const (iname, ils) ->
                    let new_fn = Const (replace_prefix n auxi iname, ils) in
                    Some (mk_app (mk_app new_fn (app_args new_nested)) rest)
                  | _ -> fail "failed to restore nested inductive types")
               | None -> None)
          | _ -> None in
      let e' = replace f !cur in
      if is_pi0 then mk_pi as_ e' else mk_lam as_ e' in
    let g_types = List.filteri (fun i _ -> i < ntypes) aux.g_types
                  |> List.map (fun (ci : decl) -> match ci.kind with
                      | Induct iv -> { ci with kind = Induct { iv with all = all_names } }
                      | _ -> assert false) in
    let orig_ctor_names = List.concat_map (fun t -> List.map fst t.it_ctors) d.d_types in
    let g_ctors = List.filter (fun (ci : decl) -> List.mem ci.name orig_ctor_names) aux.g_ctors
                  |> List.map (fun (ci : decl) -> { ci with ty = restore_nested ci.ty }) in
    let g_recs = List.map (fun (ci : decl) ->
        let renamed = List.assoc_opt ci.name aux_rec_map in
        let new_name = match renamed with Some n -> n | None -> ci.name in
        match ci.kind with
        | Rec r ->
          let rules = List.map (fun rl ->
              { r_ctor = (if renamed <> None then restore_ctor_name rl.r_ctor else rl.r_ctor);
                r_nfields = rl.r_nfields; r_rhs = restore_nested rl.r_rhs }) r.rules in
          { ci with name = new_name; ty = restore_nested ci.ty; kind = Rec { r with rall = all_names; rules } }
        | _ -> assert false) aux.g_recs in
    (* discard the auxiliary environment, install the restored declarations,
       and re-check the restored terms in it *)
    Hashtbl.reset env;
    Hashtbl.iter (fun k v -> Hashtbl.replace env k v) before;
    incr env_version; clear_caches ();
    List.iter add_decl (g_types @ g_ctors @ g_recs);
    let safety = if d.d_unsafe then Unsafe else Safe in
    with_lps d.d_lparams safety (fun () ->
        List.iter (fun (_, nested) -> ignore (infer nested)) res.nr_aux;
        List.iter (fun (ci : decl) -> ignore (infer ci.ty)) g_ctors);
    List.iter (fun (ci : decl) ->
        with_lps ci.lparams safety (fun () ->
            ignore (infer ci.ty);
            match ci.kind with
            | Rec r -> List.iter (fun rl -> ignore (infer rl.r_rhs)) r.rules
            | _ -> ())) g_recs;
    { g_types; g_ctors; g_recs }
  end

(* ----------------------------------------------------------------- quot *)
let check_quot (l : decl list) =
  let eq_n = n_ "Eq" and refl_n = n_ "Eq.refl" in
  let eq_d = match find eq_n with
    | Some ({ kind = Induct { ctors = [r]; _ }; lparams = [_]; _ } as d) when r = refl_n -> d
    | _ -> fail "failed to initialize quot module, environment does not have a suitable 'Eq' type" in
  let ue = Param (List.hd eq_d.lparams) in
  if not (eq_d.ty = Pi (Sort ue, Pi (Bvar 0, Pi (Bvar 1, prop)))) then
    fail "failed to initialize quot module, 'Eq' has an unexpected type";
  (match find refl_n with
   | Some { lparams = [v]; kind = Ctor _; ty; _ } ->
     let u = Param v in
     if not (ty = Pi (Sort u, Pi (Bvar 0, App (App (App (Const (eq_n, [u]), Bvar 1), Bvar 0), Bvar 0)))) then
       fail "failed to initialize quot module, unexpected type for 'Eq.refl'"
   | _ -> fail "failed to initialize quot module, unexpected 'Eq' constructor");
  let un = [S "u"] and vn = [S "v"] in
  let u = Param un and v = Param vn in
  let quot_n = n_ "Quot" and mk_n = n_ "Quot.mk" and lift_n = n_ "Quot.lift" and ind_n = n_ "Quot.ind" in
  (* built with free variables, so that no de Bruijn index is written by hand *)
  let loc ty = fresh_fvar ty in
  let rel a = Pi (a, Pi (a, prop)) in               (* closed a: a -> a -> Prop *)
  let alpha = loc (Sort u) in
  let r = loc (rel alpha) in
  let quot a r = mk_app (Const (quot_n, [u])) [a; r] in
  let quot_ty = mk_pi [alpha; r] (Sort u) in
  let alpha_m = loc (Sort u) in
  let r_m = loc (rel alpha_m) in
  let a_m = loc alpha_m in
  let mk_ty = mk_pi [alpha_m; r_m; a_m] (quot alpha_m r_m) in
  let alpha_l = loc (Sort u) in
  let r_l = loc (rel alpha_l) in
  let beta_l = loc (Sort v) in
  let f_l = loc (Pi (alpha_l, beta_l)) in
  let a_ = loc alpha_l in
  let b_ = loc alpha_l in
  let h_ = loc (mk_app r_l [a_; b_]) in
  let hyp = mk_pi [a_; b_; h_] (mk_app (Const (eq_n, [v])) [beta_l; App (f_l, a_); App (f_l, b_)]) in
  let q_l = loc (quot alpha_l r_l) in
  let hyp_l = loc hyp in
  let lift_ty = mk_pi [alpha_l; r_l; beta_l; f_l; hyp_l; q_l] beta_l in
  let alpha_i = loc (Sort u) in
  let r_i = loc (rel alpha_i) in
  let beta_i = loc (Pi (quot alpha_i r_i, prop)) in
  let a_i = loc alpha_i in
  let mk_app_i = mk_app (Const (mk_n, [u])) [alpha_i; r_i; a_i] in
  let mk_h = loc (mk_pi [a_i] (App (beta_i, mk_app_i))) in
  let q_i = loc (quot alpha_i r_i) in
  let ind_ty = mk_pi [alpha_i; r_i; beta_i; mk_h; q_i] (App (beta_i, q_i)) in
  let expect = [ (quot_n, QType, [un], quot_ty); (mk_n, QCtor, [un], mk_ty);
                 (lift_n, QLift, [un; vn], lift_ty); (ind_n, QInd, [un], ind_ty) ] in
  if List.length l <> 4 then fail "quotient block must declare exactly Quot, Quot.mk, Quot.lift, Quot.ind";
  List.iter (fun (n, k, lps, ty) ->
      match List.find_opt (fun (d : decl) -> d.name = n) l with
      | Some d when d.kind = Quot k && d.lparams = lps && d.ty = ty -> ()
      | _ -> fail "unexpected quotient declaration '%s'" (name_to_string n)) expect;
  List.iter add_decl l

(* ---------------------------------------------------------- declarations *)
type block =
  | Single of decl
  | QuotBlock of decl list
  | IndBlock of { types : decl list; ctors : decl list; recs : decl list }

(* unsafe / partial definitions may refer to themselves and their mutual group;
   [forward] holds every unsafe or partial definition of the file by name *)
let forward : (name, decl) Hashtbl.t = Hashtbl.create 16

let check_lparams (d : decl) =
  if not (dup_free d.lparams) then fail "duplicate universe level parameter in '%s'" (name_to_string d.name)

let safety_of (d : decl) = if d.unsafe then Unsafe else Safe

let check_type (d : decl) safety =
  check_lparams d;
  if find d.name <> None then fail "'%s' is already declared" (name_to_string d.name);
  with_lps d.lparams safety (fun () -> ignore (ensure_sort (infer d.ty)))

let check_value (d : decl) safety value =
  with_lps d.lparams safety (fun () ->
      let vt = infer value in
      if not (is_def_eq vt d.ty) then fail "type mismatch in declaration '%s'" (name_to_string d.name))

let check_block (b : block) : unit =
  match b with
  | Single d ->
    (match d.kind with
     | Axiom -> check_type d (safety_of d); add_decl d
     | Thm { value } ->
       check_type d Safe;
       if not (with_lps d.lparams Safe (fun () -> is_prop_term d.ty)) then
         fail "theorem '%s' type is not a proposition" (name_to_string d.name);
       check_value d Safe value; add_decl d
     | Opaq { value } ->
       check_type d (safety_of d); check_value d (safety_of d) value; add_decl d
     | Defn { value; safety; all; _ } ->
       (match safety with
        | Safe -> check_type d Safe; check_value d Safe value; add_decl d
        | _ ->
          check_type d safety;
          (* the body may use the declaration itself and its mutual group *)
          let temp = ref [] in
          let add_temp (x : decl) = if find x.name = None then (Hashtbl.replace env x.name x; temp := x.name :: !temp) in
          add_temp d;
          List.iter (fun n ->
              match Hashtbl.find_opt forward n with
              | Some ({ kind = Defn { safety = s; _ }; _ } as m) when s = safety && m.lparams = d.lparams -> add_temp m
              | _ -> ()) all;
          incr env_version; clear_caches ();
          check_value d safety value;
          List.iter (Hashtbl.remove env) !temp;
          incr env_version; clear_caches ();
          add_decl d)
     | Quot _ | Induct _ | Ctor _ | Rec _ -> fail "misplaced declaration '%s'" (name_to_string d.name))
  | QuotBlock l -> check_quot l
  | IndBlock { types; ctors; recs } ->
    let first = match types with t :: _ -> t | [] -> fail "empty inductive block" in
    let nparams = match first.kind with Induct iv -> iv.nparams | _ -> assert false in
    let d_types = List.map (fun (t : decl) ->
        match t.kind with
        | Induct iv ->
          { it_name = t.name; it_ty = t.ty;
            it_ctors = List.map (fun cn ->
                match List.find_opt (fun (c : decl) -> c.name = cn) ctors with
                | Some c -> (cn, c.ty)
                | None -> fail "constructor '%s' of '%s' is missing" (name_to_string cn) (name_to_string t.name)) iv.ctors }
        | _ -> assert false) types in
    let d = { d_lparams = first.lparams; d_nparams = nparams; d_types; d_unsafe = first.unsafe } in
    let g = add_inductive d in
    let match_lists what (gen : decl list) (exp : decl list) =
      if List.length gen <> List.length exp then
        fail "inductive block of '%s': expected %d %s, export has %d" (name_to_string first.name) (List.length gen) what (List.length exp);
      List.iter (fun (e : decl) ->
          match List.filter (fun (g : decl) -> g.name = e.name) gen with
          | [g] -> same_decl what g e
          | _ -> fail "exported %s '%s' is not derived from its inductive block" what (name_to_string e.name)) exp in
    match_lists "types" g.g_types types;
    match_lists "constructors" g.g_ctors ctors;
    match_lists "recursors" g.g_recs recs
