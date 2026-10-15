import Hindman168.OriginalFiberMetricBCH
import Lean
#print axioms Hindman168.OriginalFiberMetric.exists_lipschitz_left_pair
#print axioms Hindman168.OriginalFiberMetric.cosetMap_injective_of_comap
#print axioms Hindman168.OriginalFiberMetric.quotient_chart_metric_bounds
#print axioms Hindman168.OriginalFiberMetric.exists_cosetMap_antilipschitz

open Lean Elab Command
set_option maxRecDepth 10000
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let targets : List Name := [`Hindman168.OriginalFiberMetricBCH]
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
