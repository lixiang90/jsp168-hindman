import Hindman168.OriginalSameStepLinearizationInput
import Hindman168.OriginalFiberMetricExtension
import Hindman168.OriginalFiberMetricRational

/-! Quotient evaluation and the coefficient-independent observable extension. -/

namespace Hindman168.OriginalSameStepLinearization

open OAI.Erdos3 Module
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [FiniteDimensional ℚ L]
  {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (hs : 1 ≤ s)

noncomputable def fiberCosetInclusion : (fiberModel D hs).Space → (ambientModel D hs).Space :=
  OAI.Erdos3.cosetMap (fiberModel D hs).realLattice (ambientModel D hs).realLattice
    (modelFiberInclusion D hs) (le_of_eq (fiberRealLattice_eq_comap D hs))

noncomputable def fiberCosetEvaluation : (fiberModel D hs).Space → D.Space :=
  OAI.Erdos3.cosetMap (fiberModel D hs).realLattice D.realLattice
    (realFiberEvaluation D.filtration 1 0)
    (NilpotentLieBCHGroup.realificationMap_subgroup (fiberEvaluationLie D.filtration 1 0)
      (fiberModel D hs).lattice D.lattice (fiberEvaluation_lattice D hs))

noncomputable def evaluationHeight : ℕ := by
  classical
  exact Finset.univ.sup (fun z : Fin d × Fin (finrank ℚ (Fiber D.filtration 1)) =>
    let q := D.basis.repr (fiberEvaluationLie D.filtration 1 0 (fiberBasis D z.2)) z.1
    max q.num.natAbs q.den)

theorem evaluationHeight_bound (i j) :
    RationalHeightLE (D.basis.repr (fiberEvaluationLie D.filtration 1 0 (fiberBasis D j)) i)
      (evaluationHeight D) := by
  classical
  have h := Finset.le_sup (f := fun z : Fin d × Fin (finrank ℚ (Fiber D.filtration 1)) =>
    let q := D.basis.repr (fiberEvaluationLie D.filtration 1 0 (fiberBasis D z.2)) z.1
    max q.num.natAbs q.den) (Finset.mem_univ (i, j))
  exact ⟨(Nat.le_max_left _ _).trans h, (Nat.le_max_right _ _).trans h⟩

noncomputable def evaluationLipschitzBound : ℝ≥0 :=
  coordinateLipschitzBound d (finrank ℚ (Fiber D.filtration 1)) (evaluationHeight D)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] Fiber D.filtration 1)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] Fiber D.filtration 1)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Fiber D.filtration 1)]
  [T2Space (ℝ ⊗[ℚ] Fiber D.filtration 1)]

theorem fiberCosetEvaluation_lipschitz :
    letI := (fiberModel D hs).metricSpace
    letI := D.metricSpace
    LipschitzWith (evaluationLipschitzBound D) (fiberCosetEvaluation D hs) := by
  letI := (fiberModel D hs).metricSpace
  letI := D.metricSpace
  have h := NilpotentLieBCHGroup.lipschitz_realificationMap_quotient
      (fiberBasis D) D.basis (fiberEvaluationLie D.filtration 1 0)
      (fiberModel D hs).lattice D.lattice (fiberEvaluation_lattice D hs)
      (fiberModel D hs).grid D.grid (fiberModel D hs).grid_pos D.grid_pos
      (fiberModel D hs).outer_grid D.outer_grid (evaluationHeight D) (evaluationHeight_bound D)
  simp only [Fintype.card_fin] at h
  exact h

variable [TopologicalSpace (ℝ ⊗[ℚ] Algebra D.filtration 1)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra D.filtration 1)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra D.filtration 1)]
  [T2Space (ℝ ⊗[ℚ] Algebra D.filtration 1)]

/-- The analytic final step, once the independently proved ambient inverse
    metric bound is supplied. This helper preserves all integer evaluations
    and the unit norm bound exactly. -/
theorem linearize_with_inverseMetric (C : ℝ≥0)
    (hc : letI := (fiberModel D hs).metricSpace
      letI := (ambientModel D hs).metricSpace
      AntilipschitzWith C (fiberCosetInclusion D hs))
    (T : D.Niltest (fun _ : Unit => 1)) (hnorm : T.normBound ≤ 1) :
    letI := (ambientModel D hs).metricSpace
    ∃ (g x : (ambientModel D hs).RealGroup) (F : C((ambientModel D hs).Space, ℂ)),
      LipschitzWith (4 * ((T.lipBound * evaluationLipschitzBound D) * C)) F ∧
      (∀ y, ‖F y‖ ≤ 1) ∧
      ∀ n : ℤ, F (QuotientGroup.mk (g ^ n * x)) = T.eval (fun _ => n) := by
  letI := (fiberModel D hs).metricSpace
  letI := (ambientModel D hs).metricSpace
  letI := D.metricSpace
  have hG : LipschitzWith (T.lipBound * evaluationLipschitzBound D)
      (T.observable ∘ fiberCosetEvaluation D hs) :=
    T.lipschitz.comp (fiberCosetEvaluation_lipschitz D hs)
  obtain ⟨F, hF, hnF, hrestrict⟩ := OriginalFiberMetric.extend_observable
    (fiberCosetInclusion D hs) hc (T.observable ∘ fiberCosetEvaluation D hs) hG
    (fun y => (T.norm_le _).trans (by exact_mod_cast hnorm))
  obtain ⟨g, x, u, hu, hquotient⟩ := exists_linear_orbit_for_polynomial D hs T.orbit
  refine ⟨g, x, F, hF, hnF, fun n => ?_⟩
  rw [hquotient]
  change F (fiberCosetInclusion D hs (QuotientGroup.mk (u n))) = _
  rw [hrestrict]
  change T.observable (QuotientGroup.mk (realFiberEvaluation D.filtration 1 0 (u n))) = _
  rw [hu]
  rfl


/-- Uniform observable control on the fixed ambient model. The constant is
    chosen before the polynomial orbit and before its observable. -/
theorem exists_sameStep_linear_observer :
    ∃ C : ℝ≥0, ∀ T : D.Niltest (fun _ : Unit => 1), T.normBound ≤ 1 →
      letI := (ambientModel D hs).metricSpace
      ∃ (g x : (ambientModel D hs).RealGroup) (F : C((ambientModel D hs).Space, ℂ)),
        LipschitzWith (C * T.lipBound) F ∧ (∀ y, ‖F y‖ ≤ 1) ∧
        ∀ n : ℤ, F (QuotientGroup.mk (g ^ n * x)) = T.eval (fun _ => n) := by
  obtain ⟨C, hc⟩ := OriginalFiberMetric.exists_rationalCosetMap_antilipschitz
    (fiberModel D hs) (ambientModel D hs)
    (LieAlgebra.SemiDirectSum.inl (action D.filtration 1))
    (LieAlgebra.SemiDirectSum.projl (action D.filtration 1))
    (fun _ => rfl) (fiberRealLattice_eq_comap D hs)
  refine ⟨4 * (evaluationLipschitzBound D * C), fun T hn => ?_⟩
  obtain ⟨g, x, F, hF, hnorm, heval⟩ := linearize_with_inverseMetric D hs C hc T hn
  refine ⟨g, x, F, ?_, hnorm, heval⟩
  convert hF using 1 <;> ring

end Hindman168.OriginalSameStepLinearization
