import Hindman168.OriginalSupportedCubeInterval
import Lean
open Lean Elab Command
set_option maxRecDepth 10000
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let targets : List Name := [`OAI.Combinatorics.Progressions.Model, `OAI.Combinatorics.Progressions.Results.Basic, `OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans, `OAI.Combinatorics.Progressions.Estimates.WeightedSummandCorrelation, `OAI.Combinatorics.Progressions.Estimates.BufferedSiteExpansion, `OAI.Combinatorics.Progressions.Lattices.RectangularLatticeCells, `OAI.Combinatorics.Progressions.Geometry.CompactBoxIntegral, `OAI.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz, `OAI.Combinatorics.Progressions.Sampling.ModelScoreComparison, `OAI.Combinatorics.Progressions.Estimates.CorrelationDerivative, `OAI.Combinatorics.Progressions.Estimates.CyclicShortShiftSet, `OAI.Combinatorics.Progressions.Estimates.UnitExpansionCorrelation, `OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget, `OAI.Combinatorics.Progressions.Geometry.BoxDetectionExponents, `OAI.Combinatorics.Progressions.Estimates.FixedPartnerPower, `OAI.Combinatorics.Progressions.Linear.BalancedDualBounds, `OAI.Combinatorics.Progressions.Estimates.ShiftTestingGowers, `OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest, `OAI.Combinatorics.Progressions.Probability.FiniteConditionedMass, `OAI.Combinatorics.Progressions.Estimates.DenseCorrelationPairs, `OAI.Combinatorics.Progressions.Estimates.BooleanCubeProduct, `OAI.Combinatorics.Progressions.Estimates.GowersWeightedDerivative, `OAI.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport, `Hindman168.OriginalSupportedCubeInterval]
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
