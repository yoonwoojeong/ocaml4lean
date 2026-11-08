/-
  Baseline: re-check constants with Lean's official (C++) kernel, the same way
  the lean-kernel-arena "official" checker does (`Kernel.Environment.replay`
  into an empty environment).  Unsafe constants are dropped, matching what
  Export.lean writes.

  usage: lean --run Replay.lean <Module>... [-- <decl>...]
  With `-- decls`, only those declarations and their dependencies are replayed.
-/
import Lean
open Lean

partial def closure (env : Environment) (todo : List Name) (acc : Std.HashMap Name ConstantInfo) :
    Std.HashMap Name ConstantInfo := Id.run do
  let mut acc := acc
  let mut todo := todo
  while true do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if acc.contains n then continue
      let some c := env.find? n | continue
      if c.isUnsafe then continue
      acc := acc.insert n c
      let mut deps := c.type.getUsedConstants.toList
      if let some v := c.value? (allowOpaque := true) then deps := deps ++ v.getUsedConstants.toList
      match c with
      | .inductInfo v => deps := deps ++ v.all ++ v.ctors ++ v.all.map (· ++ `rec)
      | .ctorInfo v => deps := deps ++ [v.induct]
      | .recInfo v => deps := deps ++ v.all ++ (v.rules.map (·.rhs.getUsedConstants.toList)).flatten
      | .quotInfo _ => deps := deps ++ [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind, ``Eq]
      | _ => pure ()
      todo := deps ++ todo
  return acc

def main (args : List String) : IO Unit := do
  let (modArgs, declArgs) := match args.span (· != "--") with
    | (m, _ :: d) => (m, some d)
    | (m, []) => (m, none)
  let mods := modArgs.toArray.map fun s => ({ module := s.toName } : Import)
  initSearchPath (← findSysroot)
  let env ← importModules mods {} (trustLevel := 1024)
  let mut m : Std.HashMap Name ConstantInfo := {}
  match declArgs with
  | some ds => m := closure env (ds.map String.toName) {}
  | none =>
    for (n, c) in env.constants.toList do
      if !c.isUnsafe then m := m.insert n c
  -- the kernel adds the whole quotient package for `Quot`
  m := m.erase ``Quot.mk |>.erase ``Quot.lift |>.erase ``Quot.ind
  let t0 ← IO.monoNanosNow
  let empty ← mkEmptyEnvironment
  discard <| empty.toKernelEnv.replay m
  let t1 ← IO.monoNanosNow
  IO.println s!"official kernel: replayed {m.size} constants in {(t1 - t0).toFloat / 1.0e9}s"
