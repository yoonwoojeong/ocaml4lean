/-
  Baseline: re-check every constant of the given modules with Lean's official
  (C++) kernel, the same way the lean-kernel-arena "official" checker does
  (`Kernel.Environment.replay` into an empty environment).  Unsafe constants are
  dropped, matching what Export.lean writes.

  usage: lean --run Replay.lean <Module>...
-/
import Lean
open Lean

def main (args : List String) : IO Unit := do
  let mods := args.toArray.map fun s => ({ module := s.toName } : Import)
  initSearchPath (← findSysroot)
  let env ← importModules mods {} (trustLevel := 1024)
  let mut m : Std.HashMap Name ConstantInfo := {}
  for (n, c) in env.constants.toList do
    if !c.isUnsafe then m := m.insert n c
  -- the kernel adds the whole quotient package for `Quot`
  m := m.erase ``Quot.mk |>.erase ``Quot.lift |>.erase ``Quot.ind
  let t0 ← IO.monoMsNow
  let empty ← mkEmptyEnvironment
  discard <| empty.toKernelEnv.replay m
  let t1 ← IO.monoMsNow
  IO.println s!"official kernel: replayed {m.size} constants in {(t1 - t0).toFloat / 1000.0}s"
