import Hindman168.OriginalSameStepLinearizationOrbit
import Hindman168.OriginalSameStepLinearizationConjugation
import Hindman168.OriginalSameStepLinearizationSplit
import Hindman168.OriginalSameStepLinearizationTaylor
import Hindman168.OriginalSameStepLinearizationFiberTaylor
import Hindman168.OriginalSameStepLinearizationTime
import Hindman168.OriginalSameStepLinearizationRealTime
import Hindman168.OriginalSameStepLinearizationAlgebra
import Hindman168.OriginalSameStepLinearizationTranslation
import Hindman168.OriginalSameStepLinearizationReal
import Hindman168.OriginalSameStepLinearizationRealOrbit
import Hindman168.OriginalSameStepLinearizationGrid
import Hindman168.OriginalSameStepLinearizationVariable
import Hindman168.OriginalSameStepLinearizationCalculus
import Hindman168.OriginalSameStepLinearizationBasis
import Hindman168.OriginalSameStepLinearizationSymbol
import Hindman168.OriginalSameStepLinearizationRealization
import Lean
open Lean Elab Command
set_option maxRecDepth 10000
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let targets : List Name := [`Hindman168.OriginalSameStepLinearizationOrbit, `Hindman168.OriginalSameStepLinearizationConjugation, `Hindman168.OriginalSameStepLinearizationSplit, `Hindman168.OriginalSameStepLinearizationTaylor, `Hindman168.OriginalSameStepLinearizationFiberTaylor, `Hindman168.OriginalSameStepLinearizationTime, `Hindman168.OriginalSameStepLinearizationRealTime, `Hindman168.OriginalSameStepLinearizationAlgebra, `Hindman168.OriginalSameStepLinearizationTranslation, `Hindman168.OriginalSameStepLinearizationReal, `Hindman168.OriginalSameStepLinearizationRealOrbit, `Hindman168.OriginalSameStepLinearizationGrid, `Hindman168.OriginalSameStepLinearizationVariable, `Hindman168.OriginalSameStepLinearizationCalculus, `Hindman168.OriginalSameStepLinearizationBasis, `Hindman168.OriginalSameStepLinearizationSymbol, `Hindman168.OriginalSameStepLinearizationRealization]
  for target in targets do
    unless env.header.moduleNames.contains target do
      throwError m!"Missing audit module {target}"
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
  unless count > 0 do
    throwError "Empty audit"
  logInfo m!"AUDIT COMPLETE: {targets.length} modules; {count} declarations; only standard axioms"
