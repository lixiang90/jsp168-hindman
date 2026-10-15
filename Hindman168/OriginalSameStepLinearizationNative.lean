import Hindman168.OriginalSameStepLinearizationObservable
import Hindman168.OriginalBoundedNativeModelsMetric

/-! A single genuine native model is fixed before every polynomial niltest on
one prescribed rational geometry. Together with the finite geometry menu,
this gives a finite list independent of interval length and coefficients. -/

namespace Hindman168.OriginalSameStepLinearization

open OAI.Erdos3 Module
open scoped TensorProduct NNReal

variable {L : Type} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L s d) (hs : 1 ≤ s)

include hs

/-- The fixed-model, same-step polynomial-to-linear theorem. Its model is a
    real, connected, simply connected nilpotent Lie group with a genuinely
    discrete cocompact lattice and the proved compatible quotient metric. -/
theorem exists_fixed_native_linearization :
    ∃ M : NativeNilmanifoldData.{0} s, ∃ C : ℝ≥0,
      ∀ T : D.Niltest (fun _ : Unit => 1), T.normBound ≤ 1 →
        letI := M.metric
        ∃ (obs : C(M.G ⧸ M.Γ, ℂ)) (g x : M.G),
          (∀ y, ‖obs y‖ ≤ 1) ∧ LipschitzWith (C * T.lipBound) obs ∧
          ∀ n : ℤ, obs (QuotientGroup.mk (g ^ n * x)) = T.eval (fun _ => n) := by
  letI : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  obtain ⟨τF, hFA, hFS, hFT, _⟩ := exists_realification_topology_of_grid
    (fiberModel D hs).basis (fiberModel D hs).lattice (fiberModel D hs).grid
    (fiberModel D hs).grid_pos (fiberModel D hs).outer_grid
  letI : TopologicalSpace (ℝ ⊗[ℚ] Fiber D.filtration 1) := τF
  letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] Fiber D.filtration 1) := hFA
  letI : ContinuousSMul ℝ (ℝ ⊗[ℚ] Fiber D.filtration 1) := hFS
  letI : T2Space (ℝ ⊗[ℚ] Fiber D.filtration 1) := hFT
  obtain ⟨τA, hAA, hAS, hAT, _⟩ := exists_realification_topology_of_grid
    (ambientModel D hs).basis (ambientModel D hs).lattice (ambientModel D hs).grid
    (ambientModel D hs).grid_pos (ambientModel D hs).outer_grid
  letI : TopologicalSpace (ℝ ⊗[ℚ] Algebra D.filtration 1) := τA
  letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra D.filtration 1) := hAA
  letI : ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra D.filtration 1) := hAS
  letI : T2Space (ℝ ⊗[ℚ] Algebra D.filtration 1) := hAT
  obtain ⟨C, hC⟩ := exists_sameStep_linear_observer D hs
  let M := OriginalBoundedNativeModels.nativeModel (ambientModel D hs)
  refine ⟨M, C, fun T hn => ?_⟩
  obtain ⟨g, x, F, hF, hnorm, heval⟩ := hC T hn
  exact ⟨F, g, x, hnorm, hF, heval⟩

end Hindman168.OriginalSameStepLinearization
