(* Kernel expressions: locally nameless, de Bruijn indices for bound variables,
   hash-consed.  Binder names and binder infos are not stored: they have no
   influence on type checking, and dropping them makes alpha-equivalent terms
   physically equal.

   [i] packs cached data:  bit 0 = has free variables,  bit 1 = has universe
   parameters,  bit 2 = node lives in the global hash-cons tier,
   bits 3.. = loose bound variable range (1 + max loose index). *)

type t =
  | BVar of { h : int; i : int; idx : int }
  | FVar of { h : int; i : int; id : int; ty : t; v : t option }
  | Sort of { h : int; i : int; l : Level.t }
  | Const of { h : int; i : int; n : Name.t; ls : Level.t list }
  | App of { h : int; i : int; f : t; a : t }
  | Lam of { h : int; i : int; ty : t; b : t }
  | Pi of { h : int; i : int; ty : t; b : t }
  | Let of { h : int; i : int; ty : t; v : t; b : t }
  | NatLit of { h : int; i : int; n : Z.t }
  | StrLit of { h : int; i : int; s : string }
  | Proj of { h : int; i : int; s : Name.t; idx : int; e : t }

let hash = function
  | BVar { h; _ } | FVar { h; _ } | Sort { h; _ } | Const { h; _ } | App { h; _ }
  | Lam { h; _ } | Pi { h; _ } | Let { h; _ } | NatLit { h; _ } | StrLit { h; _ }
  | Proj { h; _ } -> h

let info = function
  | BVar { i; _ } | FVar { i; _ } | Sort { i; _ } | Const { i; _ } | App { i; _ }
  | Lam { i; _ } | Pi { i; _ } | Let { i; _ } | NatLit { i; _ } | StrLit { i; _ }
  | Proj { i; _ } -> i

let lbr e = info e lsr 3
let has_fvar e = info e land 1 <> 0
let has_lparam e = info e land 2 <> 0
let is_global e = info e land 4 <> 0
let closed e = info e < 8                      (* no loose bvars *)

module H = Hc.Make (struct
    type nonrec t = t
    let equal a b = match a, b with
      | BVar x, BVar y -> x.idx = y.idx
      | FVar x, FVar y -> x.id = y.id
      | Sort x, Sort y -> x.l == y.l
      | Const x, Const y ->
        x.n == y.n &&
        (let rec go a b = match a, b with
            | [], [] -> true
            | p :: a, q :: b -> p == q && go a b
            | _ -> false in go x.ls y.ls)
      | App x, App y -> x.f == y.f && x.a == y.a
      | Lam x, Lam y -> x.ty == y.ty && x.b == y.b
      | Pi x, Pi y -> x.ty == y.ty && x.b == y.b
      | Let x, Let y -> x.ty == y.ty && x.v == y.v && x.b == y.b
      | NatLit x, NatLit y -> Z.equal x.n y.n
      | StrLit x, StrLit y -> String.equal x.s y.s
      | Proj x, Proj y -> x.s == y.s && x.idx = y.idx && x.e == y.e
      | _ -> false
    let hash = hash
    let dummy = BVar { h = 0; i = 0; idx = 0 }
  end)

let mix = Hc.mix
let gbit () = if !Hc.frozen then 0 else 4
let mk_info ~fv ~lp ~lbr = (lbr lsl 3) lor (if fv then 1 else 0) lor (if lp then 2 else 0) lor gbit ()
let union a b = (max (a lsr 3) (b lsr 3) lsl 3) lor ((a lor b) land 3) lor gbit ()
(* info of a binder body: loose range decreases by one *)
let under i = let r = i lsr 3 in ((if r > 0 then r - 1 else 0) lsl 3) lor (i land 3)
let g2 a b = info a land info b land 4 <> 0
let g3 a b c = info a land info b land info c land 4 <> 0

let bvar idx = H.intern_g true (BVar { h = mix 101 idx; i = mk_info ~fv:false ~lp:false ~lbr:(idx + 1); idx })
let sort l = H.intern_g true (Sort { h = mix 103 (Level.hash l); i = mk_info ~fv:false ~lp:(Level.has_param l) ~lbr:0; l })
let const n ls =
  let h = List.fold_left (fun h l -> mix h (Level.hash l)) (mix 107 (Name.hash n)) ls in
  H.intern_g true (Const { h; i = mk_info ~fv:false ~lp:(List.exists Level.has_param ls) ~lbr:0; n; ls })
(* After parsing, new nodes are shared only with the (frozen) environment tier;
   see Hc.intern_g.  A node can only be in that tier if all its children are. *)
let app f a =
  H.intern_g (g2 f a) (App { h = mix (mix 109 (hash f)) (hash a); i = union (info f) (info a); f; a })
let lam ty b =
  H.intern_g (g2 ty b) (Lam { h = mix (mix 113 (hash ty)) (hash b); i = union (info ty) (under (info b)); ty; b })
let pi ty b =
  H.intern_g (g2 ty b) (Pi { h = mix (mix 127 (hash ty)) (hash b); i = union (info ty) (under (info b)); ty; b })
let let_ ty v b =
  H.intern_g (g3 ty v b)
    (Let { h = mix (mix (mix 131 (hash ty)) (hash v)) (hash b);
           i = union (union (info ty) (info v)) (under (info b)); ty; v; b })
let natlit n = H.intern_g true (NatLit { h = mix 137 (Z.hash n); i = gbit (); n })
let strlit s = H.intern_g true (StrLit { h = mix 139 (Hashtbl.hash s); i = gbit (); s })
let proj s idx e =
  H.intern_g (is_global e) (Proj { h = mix (mix (mix 149 (Name.hash s)) idx) (hash e); i = (info e land (lnot 4)) lor gbit (); s; idx; e })

(* Free variables are never shared between domains: per-domain counter. *)
let fv_counter = Domain.DLS.new_key (fun () -> ref 0)
let mk_fvar ?v ty =
  let c = Domain.DLS.get fv_counter in
  incr c;
  let id = !c in
  FVar { h = mix 151 id; i = 1; id; ty; v }

let fvar_ty = function FVar { ty; _ } -> ty | _ -> invalid_arg "fvar_ty"

(* ---------- structural equality ----------
   Free-variable-free nodes are hash-consed, so for them physical equality is
   structural equality.  Two terms can only be equal if both or neither contain
   free variables; only then is a structural walk needed.  The walk is
   memoised once it gets large, so shared sub-DAGs are not unfolded. *)
module PairTbl = Hashtbl.Make (struct
    type nonrec t = t * t
    let equal (a, b) (c, d) = a == c && b == d
    let hash (a, b) = mix (hash a) (hash b)
  end)

let equal a b =
  a == b ||
  (hash a = hash b && not (is_global a && is_global b) &&
   (let budget = ref 4096 in
    let memo = ref None in
    let rec eq a b =
      a == b ||
      (hash a = hash b && not (is_global a && is_global b) &&
       begin
         decr budget;
         if !budget < 0 then begin
           let m = match !memo with Some m -> m | None -> let m = PairTbl.create 256 in memo := Some m; m in
           if PairTbl.mem m (a, b) then true
           else begin
             let r = shallow a b in
             if r then PairTbl.replace m (a, b) ();
             r
           end
         end else shallow a b
       end)
    and shallow a b = match a, b with
      | BVar x, BVar y -> x.idx = y.idx
      | FVar x, FVar y -> x.id = y.id
      | Sort x, Sort y -> Level.equal x.l y.l
      | Const x, Const y ->
        Name.equal x.n y.n && List.compare_lengths x.ls y.ls = 0 && List.for_all2 Level.equal x.ls y.ls
      | App x, App y -> eq x.f y.f && eq x.a y.a
      | Lam x, Lam y -> eq x.ty y.ty && eq x.b y.b
      | Pi x, Pi y -> eq x.ty y.ty && eq x.b y.b
      | Let x, Let y -> eq x.ty y.ty && eq x.v y.v && eq x.b y.b
      | NatLit x, NatLit y -> Z.equal x.n y.n
      | StrLit x, StrLit y -> String.equal x.s y.s
      | Proj x, Proj y -> Name.equal x.s y.s && x.idx = y.idx && eq x.e y.e
      | _ -> false in
    shallow a b))

(* ---------- application spines ---------- *)
let rec get_app_fn = function App { f; _ } -> get_app_fn f | e -> e
let rec get_app_num_args e = match e with App { f; _ } -> 1 + get_app_num_args f | _ -> 0

(* returns head and args in application order *)
let get_app_args e =
  let n = get_app_num_args e in
  let args = Array.make n e in
  let rec go e k = match e with
    | App { f; a; _ } -> args.(k) <- a; go f (k - 1)
    | _ -> e in
  let f = go e (n - 1) in
  (f, args)

let mk_app_arr f args = Array.fold_left app f args
let mk_app_sub f args lo hi = (* args.(lo) .. args.(hi-1) *)
  let r = ref f in for k = lo to hi - 1 do r := app !r args.(k) done; !r
let mk_app_list f args = List.fold_left app f args

let is_app_of e n = match get_app_fn e with Const { n = m; _ } -> m == n || Name.equal m n | _ -> false

(* ---------- caches for traversals over DAGs ---------- *)
module Tbl = Hashtbl.Make (struct type nonrec t = t let equal = equal let hash = hash end)
module PhysTbl = Hashtbl.Make (struct type nonrec t = t let equal = ( == ) let hash = hash end)
module Tbl2 = Hashtbl.Make (struct
    type nonrec t = t * int
    let equal (a, i) (b, j) = a == b && i = j
    let hash (a, i) = mix (hash a) i
  end)

(* Lossy, direct-mapped memo table keyed by (node, offset), one per domain and
   traversal kind.  Entries are invalidated in O(1) by bumping a generation
   counter, so starting a traversal allocates nothing.  Being lossy only costs
   recomputation: results never depend on whether an entry is present. *)
module Memo = struct
  let bits = 14
  let size = 1 lsl bits
  type m = { ks : t array; offs : int array; gens : int array; vs : t array; mutable gen : int }
  let dummy = BVar { h = 0; i = 0; idx = 0 }
  let create () = { ks = Array.make size dummy; offs = Array.make size 0; gens = Array.make size 0;
                    vs = Array.make size dummy; gen = 0 }
  let start m = m.gen <- m.gen + 1
  let slot e off = (mix (hash e) off) land (size - 1)
  let find m e off =
    let i = slot e off in
    if Array.unsafe_get m.gens i = m.gen && Array.unsafe_get m.ks i == e && Array.unsafe_get m.offs i = off
    then Array.unsafe_get m.vs i else raise Not_found
  let add m e off v =
    let i = slot e off in
    Array.unsafe_set m.gens i m.gen; Array.unsafe_set m.ks i e;
    Array.unsafe_set m.offs i off; Array.unsafe_set m.vs i v
  (* Generations make the arrays retain dead nodes only up to [size] entries. *)
  let key = Domain.DLS.new_key (fun () -> Array.init 6 (fun _ -> create ()))
  let get k = let m = (Domain.DLS.get key).(k) in start m; m
end

(* lift loose bvars >= s by d *)
let lift_loose e s d =
  if d = 0 || lbr e <= s then e else begin
    let cache = Tbl2.create 16 in
    let rec go e off =
      if lbr e <= s + off then e else
        match Tbl2.find cache (e, off) with
        | r -> r
        | exception Not_found ->
          let r = match e with
            | BVar { idx; _ } -> bvar (idx + d)
            | App { f; a; _ } -> app (go f off) (go a off)
            | Lam { ty; b; _ } -> lam (go ty off) (go b (off + 1))
            | Pi { ty; b; _ } -> pi (go ty off) (go b (off + 1))
            | Let { ty; v; b; _ } -> let_ (go ty off) (go v off) (go b (off + 1))
            | Proj { s; idx; e; _ } -> proj s idx (go e off)
            | _ -> e in
          Tbl2.add cache (e, off) r; r in
    go e 0
  end

(* lower loose bvars >= s by d (caller guarantees no bvar in [s-d, s) occurs) *)
let lower_loose e s d =
  if d = 0 || lbr e <= s then e else begin
    let cache = Tbl2.create 16 in
    let rec go e off =
      if lbr e <= s + off then e else
        match Tbl2.find cache (e, off) with
        | r -> r
        | exception Not_found ->
          let r = match e with
            | BVar { idx; _ } -> bvar (idx - d)
            | App { f; a; _ } -> app (go f off) (go a off)
            | Lam { ty; b; _ } -> lam (go ty off) (go b (off + 1))
            | Pi { ty; b; _ } -> pi (go ty off) (go b (off + 1))
            | Let { ty; v; b; _ } -> let_ (go ty off) (go v off) (go b (off + 1))
            | Proj { s; idx; e; _ } -> proj s idx (go e off)
            | _ -> e in
          Tbl2.add cache (e, off) r; r in
    go e 0
  end

(* instantiate e with subst: loose bvar (off + k) for k < n becomes subst k
   (lifted by off), bvar (off + k) for k >= n becomes bvar (off + k - n).
   [subst k] = arr.(base - k) if [rev] else arr.(base + k). *)
let instantiate_core e n (arr : t array) base rev =
  if closed e || n = 0 then e else begin
    let cache = Tbl2.create 32 in
    let get k = if rev then Array.unsafe_get arr (base - k) else Array.unsafe_get arr (base + k) in
    let rec go e off =
      if lbr e <= off then e else
        match e with
        | BVar { idx; _ } ->
          let k = idx - off in
          if k < n then lift_loose (get k) 0 off else bvar (idx - n)
        | _ ->
          match Tbl2.find cache (e, off) with
          | r -> r
          | exception Not_found ->
            let r = match e with
              | App { f; a; _ } -> app (go f off) (go a off)
              | Lam { ty; b; _ } -> lam (go ty off) (go b (off + 1))
              | Pi { ty; b; _ } -> pi (go ty off) (go b (off + 1))
              | Let { ty; v; b; _ } -> let_ (go ty off) (go v off) (go b (off + 1))
              | Proj { s; idx; e; _ } -> proj s idx (go e off)
              | _ -> e in
            Tbl2.add cache (e, off) r; r in
    go e 0
  end

let instantiate_gen e n (get : int -> t) = instantiate_core e n (Array.init n get) 0 false

(* bvar 0 := v *)
let instantiate1 e v =
  if closed e then e else begin
    let cache = Tbl2.create 32 in
    let rec go e off =
      if lbr e <= off then e else
        match e with
        | BVar { idx; _ } -> if idx = off then lift_loose v 0 off else bvar (idx - 1)
        | _ ->
          match Tbl2.find cache (e, off) with
          | r -> r
          | exception Not_found ->
            let r = match e with
              | App { f; a; _ } -> app (go f off) (go a off)
              | Lam { ty; b; _ } -> lam (go ty off) (go b (off + 1))
              | Pi { ty; b; _ } -> pi (go ty off) (go b (off + 1))
              | Let { ty; v; b; _ } -> let_ (go ty off) (go v off) (go b (off + 1))
              | Proj { s; idx; e; _ } -> proj s idx (go e off)
              | _ -> e in
            Tbl2.add cache (e, off) r; r in
    go e 0
  end

(* Lean's instantiate(e, n, s): bvar k := s.(k) *)
let instantiate e (s : t array) = instantiate_core e (Array.length s) s 0 false
(* Lean's instantiate_rev(e, n, s): bvar k := s.(n-1-k) *)
let instantiate_rev e (s : t array) =
  let n = Array.length s in instantiate_core e n s (n - 1) true
let instantiate_rev_sub e (s : t array) n = instantiate_core e n s (n - 1) true
(* bvar k := args.(hi - 1 - k) for k < hi - lo: the arguments args.(lo..hi-1) as a
   reversed substitution, as used for beta reduction of [f args] *)
let instantiate_args e (args : t array) lo hi = instantiate_core e (hi - lo) args (hi - 1) true

(* abstract fvars xs.(0..n-1): fvar xs.(j) becomes bvar (off + n - 1 - j) *)
let abstract e (xs : t array) n =
  if not (has_fvar e) || n = 0 then e else begin
    let cache = Tbl2.create 32 in
    let find_idx id =
      let rec find j = if j < 0 then -1 else
          (match Array.unsafe_get xs j with FVar x when x.id = id -> j | _ -> find (j - 1)) in
      find (n - 1) in
    let rec go e off =
      if not (has_fvar e) then e else
        match e with
        | FVar { id; _ } ->
          let j = find_idx id in if j < 0 then e else bvar (off + n - 1 - j)
        | _ ->
          match Tbl2.find cache (e, off) with
          | r -> r
          | exception Not_found ->
            let r = match e with
              | App { f; a; _ } -> app (go f off) (go a off)
              | Lam { ty; b; _ } -> lam (go ty off) (go b (off + 1))
              | Pi { ty; b; _ } -> pi (go ty off) (go b (off + 1))
              | Let { ty; v; b; _ } -> let_ (go ty off) (go v off) (go b (off + 1))
              | Proj { s; idx; e; _ } -> proj s idx (go e off)
              | _ -> e in
            Tbl2.add cache (e, off) r; r in
    go e 0
  end

let has_loose_bvar0 e =
  (* does bvar 0 occur loosely? *)
  if closed e then false else begin
    let seen = Tbl2.create 16 in
    let rec go e off =
      if lbr e <= off then false
      else match e with
        | BVar { idx; _ } -> idx = off
        | _ ->
          if Tbl2.mem seen (e, off) then false else begin
            Tbl2.add seen (e, off) ();
            match e with
            | App { f; a; _ } -> go f off || go a off
            | Lam { ty; b; _ } | Pi { ty; b; _ } -> go ty off || go b (off + 1)
            | Let { ty; v; b; _ } -> go ty off || go v off || go b (off + 1)
            | Proj { e; _ } -> go e off
            | _ -> false
          end in
    go e 0
  end

(* Lean's local_ctx::mk_binding.  [is_lam] chooses lambda/pi; let-fvars become
   lets (dead ones removed when [remove_dead_let]). *)
let mk_binding is_lam (xs : t array) n b remove_dead_let =
  let r = ref (abstract b xs n) in
  for i = n - 1 downto 0 do
    match xs.(i) with
    | FVar { ty; v = Some v; _ } ->
      if (not remove_dead_let) || has_loose_bvar0 !r then
        r := let_ (abstract ty xs i) (abstract v xs i) !r
      else r := lower_loose !r 1 1
    | FVar { ty; _ } ->
      let ty = abstract ty xs i in
      r := if is_lam then lam ty !r else pi ty !r
    | _ -> assert false
  done;
  !r

let mk_pi xs b = mk_binding false xs (Array.length xs) b false
let mk_lambda xs b = mk_binding true xs (Array.length xs) b false
let mk_pi_l xs b = mk_pi (Array.of_list xs) b
let mk_lambda_l xs b = mk_lambda (Array.of_list xs) b

(* ---------- universe parameter instantiation ---------- *)
let instantiate_lparams e (ps : Name.t list) (ls : Level.t list) =
  if (match ps with [] -> true | _ -> false) || not (has_lparam e) then e else begin
    let cache = Tbl2.create 64 in
    let lv l = Level.instantiate ps ls l in
    let rec go e =
      if not (has_lparam e) then e else
        match Tbl2.find cache (e, 0) with
        | r -> r
        | exception Not_found ->
          let r = match e with
            | Sort { l; _ } -> sort (lv l)
            | Const { n; ls; _ } -> const n (List.map lv ls)
            | App { f; a; _ } -> app (go f) (go a)
            | Lam { ty; b; _ } -> lam (go ty) (go b)
            | Pi { ty; b; _ } -> pi (go ty) (go b)
            | Let { ty; v; b; _ } -> let_ (go ty) (go v) (go b)
            | Proj { s; idx; e; _ } -> proj s idx (go e)
            | _ -> e in
          Tbl2.add cache (e, 0) r; r in
    go e
  end

(* generic search: does some subterm satisfy p ? (p is applied to every node) *)
let exists p e =
  let seen = PhysTbl.create 64 in
  let rec go e =
    if PhysTbl.mem seen e then false else begin
      PhysTbl.add seen e ();
      p e || (match e with
          | App { f; a; _ } -> go f || go a
          | Lam { ty; b; _ } | Pi { ty; b; _ } -> go ty || go b
          | Let { ty; v; b; _ } -> go ty || go v || go b
          | Proj { e; _ } -> go e
          | FVar _ | BVar _ | Sort _ | Const _ | NatLit _ | StrLit _ -> false)
    end in
  go e

(* generic replace (no binder offset tracking needed by callers here) *)
let replace (f : t -> t option) e =
  let cache = PhysTbl.create 64 in
  let rec go e =
    match PhysTbl.find cache e with
    | r -> r
    | exception Not_found ->
      let r = match f e with
        | Some r -> r
        | None -> match e with
          | App { f; a; _ } -> app (go f) (go a)
          | Lam { ty; b; _ } -> lam (go ty) (go b)
          | Pi { ty; b; _ } -> pi (go ty) (go b)
          | Let { ty; v; b; _ } -> let_ (go ty) (go v) (go b)
          | Proj { s; idx; e; _ } -> proj s idx (go e)
          | _ -> e in
      PhysTbl.add cache e r; r in
  go e

(* ---------- printing (diagnostics only) ---------- *)
let to_string ?(max = 2000) e =
  let b = Buffer.create 256 in
  let rec go e =
    if Buffer.length b > max then () else
      match e with
      | BVar { idx; _ } -> Buffer.add_string b ("#" ^ string_of_int idx)
      | FVar { id; _ } -> Buffer.add_string b ("_x" ^ string_of_int id)
      | Sort { l; _ } -> Buffer.add_string b ("Sort " ^ Level.to_string l)
      | Const { n; ls; _ } ->
        Buffer.add_string b (Name.to_string n);
        if ls <> [] then Buffer.add_string b (".{" ^ String.concat ", " (List.map Level.to_string ls) ^ "}")
      | App _ ->
        let f, args = get_app_args e in
        Buffer.add_char b '('; go f;
        Array.iter (fun a -> Buffer.add_char b ' '; go a) args; Buffer.add_char b ')'
      | Lam { ty; b = bd; _ } -> Buffer.add_string b "(fun _ : "; go ty; Buffer.add_string b " => "; go bd; Buffer.add_char b ')'
      | Pi { ty; b = bd; _ } -> Buffer.add_string b "((_ : "; go ty; Buffer.add_string b ") -> "; go bd; Buffer.add_char b ')'
      | Let { ty; v; b = bd; _ } -> Buffer.add_string b "(let _ : "; go ty; Buffer.add_string b " := "; go v; Buffer.add_string b "; "; go bd; Buffer.add_char b ')'
      | NatLit { n; _ } -> Buffer.add_string b (Z.to_string n)
      | StrLit { s; _ } -> Buffer.add_string b (Printf.sprintf "%S" s)
      | Proj { s; idx; e; _ } -> go e; Buffer.add_string b ("." ^ Name.to_string s ^ "." ^ string_of_int (idx + 1)) in
  go e;
  if Buffer.length b > max then Buffer.sub b 0 max ^ "..." else Buffer.contents b
