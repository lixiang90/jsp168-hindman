import Hindman168.PositivePrincipalSumNativeIndices
import Hindman168.PositivePrincipalSumNativeAdapter
import Hindman168.PositivePrincipalSumNativePalette
import Hindman168.PositivePrincipalSumNativeEvent
import Hindman168.PositivePrincipalSumNativeReadings
import Hindman168.PositivePrincipalSumMassCover
import Hindman168.PositivePrincipalSumMassThresholds
import Hindman168.PositivePrincipalSumMassDeduction
import Hindman168.PositivePrincipalSumMassJointHaar
import Hindman168.PositivePrincipalSumMassPlanOptions
import Hindman168.PositivePrincipalSumPivotConditioning
import Hindman168.PositivePrincipalSumPivotTranslation
import Hindman168.PositivePrincipalSumPivotPaths
import Hindman168.PositivePrincipalSumPivotIteration
import Hindman168.PositivePrincipalSumPivotBoundary
import Hindman168.PositivePrincipalSumPivotMasterBoundary
import Hindman168.PositivePrincipalSumPivotMasterExtension
import Lean
open Lean Elab Command
set_option maxRecDepth 10000
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let targets : List Name := [`Hindman168.PositivePrincipalSumNativeIndices, `Hindman168.PositivePrincipalSumNativeAdapter, `Hindman168.PositivePrincipalSumNativePalette, `Hindman168.PositivePrincipalSumNativeEvent, `Hindman168.PositivePrincipalSumNativeReadings, `Hindman168.PositivePrincipalSumMassCover, `Hindman168.PositivePrincipalSumMassThresholds, `Hindman168.PositivePrincipalSumMassDeduction, `Hindman168.PositivePrincipalSumMassJointHaar, `Hindman168.PositivePrincipalSumMassPlanOptions, `Hindman168.PositivePrincipalSumPivotConditioning, `Hindman168.PositivePrincipalSumPivotTranslation, `Hindman168.PositivePrincipalSumPivotPaths, `Hindman168.PositivePrincipalSumPivotIteration, `Hindman168.PositivePrincipalSumPivotBoundary, `Hindman168.PositivePrincipalSumPivotMasterBoundary, `Hindman168.PositivePrincipalSumPivotMasterExtension]
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
