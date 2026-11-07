/-
  A small exporter producing the lean4export NDJSON format (v3.1.0), written
  for this project so that benchmarks can be generated with only a Lean
  toolchain.  Declarations are emitted in dependency order (post-order DFS);
  unsafe declarations and `mdata` are omitted, as in lean4export's default mode.

  usage: lean --run Export.lean <Module>... > out.ndjson
-/
import Lean
open Lean

structure St where
  names  : Std.HashMap Name Nat := {}
  levels : Std.HashMap Level Nat := {}
  exprs  : Std.HashMap Expr Nat := {}
  done   : Std.HashSet Name := {}
  nextE  : Nat := 0

abbrev M := StateT St (ReaderT (Environment × IO.FS.Stream) IO)

def out (j : Json) : M Unit := do
  let (_, h) ← read
  h.putStrLn j.compress

partial def dumpName (n : Name) : M Nat := do
  if n.isAnonymous then return 0
  if let some i := (← get).names[n]? then return i
  let j ← match n with
    | .str p s => do let pi ← dumpName p; pure (Json.mkObj [("str", Json.mkObj [("pre", pi), ("str", s)])])
    | .num p k => do let pi ← dumpName p; pure (Json.mkObj [("num", Json.mkObj [("pre", pi), ("i", k)])])
    | .anonymous => unreachable!
  let i := (← get).names.size + 1
  modify fun s => { s with names := s.names.insert n i }
  out (j.setObjVal! "in" i)
  return i

partial def dumpLevel (l : Level) : M Nat := do
  if l.isZero then return 0
  if let some i := (← get).levels[l]? then return i
  let j ← match l with
    | .succ a => do pure (Json.mkObj [("succ", ← dumpLevel a)])
    | .max a b => do pure (Json.mkObj [("max", Json.arr #[← dumpLevel a, ← dumpLevel b])])
    | .imax a b => do pure (Json.mkObj [("imax", Json.arr #[← dumpLevel a, ← dumpLevel b])])
    | .param n => do pure (Json.mkObj [("param", ← dumpName n)])
    | _ => throw (IO.userError "unexpected level")
  let i := (← get).levels.size + 1
  modify fun s => { s with levels := s.levels.insert l i }
  out (j.setObjVal! "il" i)
  return i

def bi : BinderInfo → Json
  | .default => "default" | .implicit => "implicit"
  | .strictImplicit => "strictImplicit" | .instImplicit => "instImplicit"

partial def dumpExpr (e : Expr) : M Nat := do
  let e := e.consumeMData
  if let some i := (← get).exprs[e]? then return i
  let j ← match e with
    | .bvar k => pure (Json.mkObj [("bvar", k)])
    | .sort l => do pure (Json.mkObj [("sort", ← dumpLevel l)])
    | .const n us => do
      let n ← dumpName n
      let us ← us.mapM dumpLevel
      pure (Json.mkObj [("const", Json.mkObj [("name", n), ("us", toJson us)])])
    | .app f a => do
      let f ← dumpExpr f; let a ← dumpExpr a
      pure (Json.mkObj [("app", Json.mkObj [("fn", f), ("arg", a)])])
    | .lam n t b i => do
      let n ← dumpName n; let t ← dumpExpr t; let b ← dumpExpr b
      pure (Json.mkObj [("lam", Json.mkObj [("name", n), ("type", t), ("body", b), ("binderInfo", bi i)])])
    | .forallE n t b i => do
      let n ← dumpName n; let t ← dumpExpr t; let b ← dumpExpr b
      pure (Json.mkObj [("forallE", Json.mkObj [("name", n), ("type", t), ("body", b), ("binderInfo", bi i)])])
    | .letE n t v b nd => do
      let n ← dumpName n; let t ← dumpExpr t; let v ← dumpExpr v; let b ← dumpExpr b
      pure (Json.mkObj [("letE", Json.mkObj [("name", n), ("type", t), ("value", v), ("body", b), ("nondep", nd)])])
    | .proj s k x => do
      let s ← dumpName s; let x ← dumpExpr x
      pure (Json.mkObj [("proj", Json.mkObj [("typeName", s), ("idx", k), ("struct", x)])])
    | .lit (.natVal k) => pure (Json.mkObj [("natVal", toString k)])
    | .lit (.strVal s) => pure (Json.mkObj [("strVal", s)])
    | _ => throw (IO.userError s!"unexpected expression {e}")
  let i := (← get).nextE
  modify fun s => { s with exprs := s.exprs.insert e i, nextE := i + 1 }
  out (j.setObjVal! "ie" i)
  return i

def getC (n : Name) : M ConstantInfo := do
  let (env, _) ← read
  match env.find? n with
  | some c => pure c
  | none => throw (IO.userError s!"unknown constant {n}")

def hintsJ : ReducibilityHints → Json
  | .opaque => "opaque" | .abbrev => "abbrev" | .regular h => Json.mkObj [("regular", h.toNat)]

def safetyJ : DefinitionSafety → Json
  | .safe => "safe" | .unsafe => "unsafe" | .partial => "partial"

/-- All members of the declaration block containing `c`. -/
def blockOf (c : ConstantInfo) : M (Array ConstantInfo) := do
  let indBlock (all : List Name) : M (Array ConstantInfo) := do
    let mut r := #[]
    let mut ctors := #[]
    let mut recs := #[]
    for t in all do
      let ti ← getC t
      r := r.push ti
      if let .inductInfo iv := ti then
        for k in iv.ctors do ctors := ctors.push (← getC k)
        recs := recs.push (← getC (t ++ `rec))
    -- auxiliary recursors of nested inductives
    if let .inductInfo iv ← getC all.head! then
      for k in [1:iv.numNested + 1] do
        recs := recs.push (← getC ((all.head! ++ `rec).appendIndexAfter k))
    return r ++ ctors ++ recs
  match c with
  | .inductInfo v => indBlock v.all
  | .ctorInfo v => do
    match ← getC v.induct with
    | .inductInfo iv => indBlock iv.all
    | _ => throw (IO.userError "bad ctor")
  | .recInfo v => indBlock v.all
  | .quotInfo _ => return #[← getC ``Quot, ← getC ``Quot.mk, ← getC ``Quot.lift, ← getC ``Quot.ind]
  | _ => return #[c]

def namesJ (ns : List Name) : M Json := do return toJson (← ns.mapM dumpName)

mutual
partial def dumpConst (n : Name) : M Unit := do
  if (← get).done.contains n then return
  let c ← getC n
  if c.isUnsafe then return
  let blk ← blockOf c
  for m in blk do modify fun s => { s with done := s.done.insert m.name }
  -- dependencies first
  for m in blk do
    for d in m.type.getUsedConstants do dumpConst d
    if let some v := m.value? (allowOpaque := true) then
      for d in v.getUsedConstants do dumpConst d
    if let .recInfo rv := m then
      for r in rv.rules do for d in r.rhs.getUsedConstants do dumpConst d
  if c matches .quotInfo _ then dumpConst ``Eq
  emitBlock blk

partial def emitBlock (blk : Array ConstantInfo) : M Unit := do
  match blk[0]! with
  | .inductInfo _ =>
    let mut types := #[]; let mut ctors := #[]; let mut recs := #[]
    for m in blk do
      let base ← pure (Json.mkObj [("name", ← dumpName m.name), ("levelParams", ← namesJ m.levelParams),
                                   ("type", ← dumpExpr m.type)])
      match m with
      | .inductInfo v =>
        types := types.push (base.mergeObj (Json.mkObj [("numParams", v.numParams), ("numIndices", v.numIndices),
          ("all", ← namesJ v.all), ("ctors", ← namesJ v.ctors), ("numNested", v.numNested),
          ("isRec", v.isRec), ("isUnsafe", v.isUnsafe), ("isReflexive", v.isReflexive)]))
      | .ctorInfo v =>
        ctors := ctors.push (base.mergeObj (Json.mkObj [("induct", ← dumpName v.induct), ("cidx", v.cidx),
          ("numParams", v.numParams), ("numFields", v.numFields), ("isUnsafe", v.isUnsafe)]))
      | .recInfo v =>
        let rules ← v.rules.mapM fun r => do
          pure (Json.mkObj [("ctor", ← dumpName r.ctor), ("nfields", r.nfields), ("rhs", ← dumpExpr r.rhs)])
        recs := recs.push (base.mergeObj (Json.mkObj [("all", ← namesJ v.all), ("numParams", v.numParams),
          ("numIndices", v.numIndices), ("numMotives", v.numMotives), ("numMinors", v.numMinors),
          ("rules", toJson rules), ("k", v.k), ("isUnsafe", v.isUnsafe)]))
      | _ => unreachable!
    out (Json.mkObj [("inductive", Json.mkObj [("types", toJson types), ("ctors", toJson ctors), ("recs", toJson recs)])])
  | _ =>
    for m in blk do
      let name ← dumpName m.name
      let lps ← namesJ m.levelParams
      let ty ← dumpExpr m.type
      match m with
      | .axiomInfo v => out (Json.mkObj [("axiom", Json.mkObj [("name", name), ("levelParams", lps), ("type", ty), ("isUnsafe", v.isUnsafe)])])
      | .defnInfo v =>
        let val ← dumpExpr v.value
        out (Json.mkObj [("def", Json.mkObj [("name", name), ("levelParams", lps), ("type", ty), ("value", val),
          ("hints", hintsJ v.hints), ("safety", safetyJ v.safety), ("all", ← namesJ v.all)])])
      | .thmInfo v =>
        let val ← dumpExpr v.value
        out (Json.mkObj [("thm", Json.mkObj [("name", name), ("levelParams", lps), ("type", ty), ("value", val), ("all", ← namesJ v.all)])])
      | .opaqueInfo v =>
        let val ← dumpExpr v.value
        out (Json.mkObj [("opaque", Json.mkObj [("name", name), ("levelParams", lps), ("type", ty), ("value", val),
          ("isUnsafe", v.isUnsafe), ("all", ← namesJ v.all)])])
      | .quotInfo v =>
        let k : Json := match v.kind with | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"
        out (Json.mkObj [("quot", Json.mkObj [("name", name), ("levelParams", lps), ("type", ty), ("kind", k)])])
      | _ => unreachable!
end

def main (args : List String) : IO Unit := do
  let mods := args.toArray.map fun s => ({ module := s.toName } : Import)
  initSearchPath (← findSysroot)
  let env ← importModules mods {} (trustLevel := 1024)
  let h ← IO.getStdout
  let act : M Unit := do
    out (Json.mkObj [("meta", Json.mkObj [("exporter", Json.mkObj [("name", "ocaml4lean-export"), ("version", "3.1.0")]),
      ("format", Json.mkObj [("version", "3.1.0")]),
      ("lean", Json.mkObj [("version", Lean.versionString), ("githash", Lean.githash)])])])
    -- deterministic order: sort constant names
    let names := env.constants.toList.map (·.1) |>.toArray.qsort Name.lt
    for n in names do dumpConst n
  discard <| (act.run {}).run (env, h)
