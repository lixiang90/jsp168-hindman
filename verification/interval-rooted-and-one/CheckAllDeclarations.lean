import Hindman168.NativePeriodicIntervalInverseOne
import Lean
open Lean Elab Command
set_option maxRecDepth 10000
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let targets : List Name := [`Hindman168.IntegerIntervalGowersZeroExtension, `Hindman168.IntegerIntervalGowersDimensionOne, `Hindman168.NativePeriodicIntervalInverseOne]
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if targets.contains env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        let axioms ← collectAxioms name
        for ax in axioms do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError m!"Unexpected axiom {ax} in {name}"
        logInfo m!"AUDIT {name}: {axioms}"
        count := count + 1
  logInfo m!"AUDIT COMPLETE: {count} declarations; only standard axioms"

example (q : ℕ) (v : ZMod q → ℝ) :
    Hindman168.integerIntervalPeriodicGowersValue q 1 0 v = 0 := by
  rw [Hindman168.integerIntervalPeriodicGowersValue_one_dimension]
  simp [Hindman168.finiteHaarMean]
