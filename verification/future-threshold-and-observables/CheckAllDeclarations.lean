import Hindman168.PositivePrincipalSumFutureScalePaths
import Hindman168.PositivePrincipalSumFutureThreshold
import Hindman168.PositivePrincipalSumFutureNative
import Hindman168.PositivePrincipalSumFutureObservation
import Hindman168.PositivePrincipalSumFutureEvent
import Hindman168.PositivePrincipalSumFutureThresholdPaths
import Hindman168.PositivePrincipalSumFutureFinal
import Hindman168.AlignmentJointObservableCompactness
import Hindman168.AlignmentJointObservableCompactnessNative
import Hindman168.AlignmentJointObservableCompactnessReadings
import Hindman168.AlignmentJointObservableCompactnessSource
import Lean
open Lean Elab Command
set_option maxRecDepth 10000
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let targets : List Name := [`Hindman168.PositivePrincipalSumFutureScalePaths, `Hindman168.PositivePrincipalSumFutureThreshold, `Hindman168.PositivePrincipalSumFutureNative, `Hindman168.PositivePrincipalSumFutureObservation, `Hindman168.PositivePrincipalSumFutureEvent, `Hindman168.PositivePrincipalSumFutureThresholdPaths, `Hindman168.PositivePrincipalSumFutureFinal, `Hindman168.AlignmentJointObservableCompactness, `Hindman168.AlignmentJointObservableCompactnessNative, `Hindman168.AlignmentJointObservableCompactnessReadings, `Hindman168.AlignmentJointObservableCompactnessSource]
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
