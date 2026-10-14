import Hindman168.CompactUnitLipschitzObservables

/-! Compactness of the ACTUAL class of uniformly bounded complex tests with
one fixed numerical Lipschitz bound. Arbitrary bounds remain explicit. -/
namespace Hindman168
open scoped NNReal

def boundedComplexLipschitzObservables (X : Type*) [PseudoMetricSpace X] (B : ℝ) (L : NNReal) :
    Set C(X,ℂ) := {f | LipschitzWith L f ∧ ∀ x, ‖f x‖ ≤ B}

theorem bounded_complex_lipschitz_observables_compact (X : Type*) [PseudoMetricSpace X]
    (B : ℝ) (L : NNReal) : IsCompact (boundedComplexLipschitzObservables X B L) := by
  let A : Set (X → ℂ) := {f | LipschitzWith L f ∧ ∀ x, ‖f x‖ ≤ B}
  have hbound : IsClosed {f : X → ℂ | ∀ x, ‖f x‖ ≤ B} := by
    simpa only [Set.setOf_forall,Function.comp_def] using
      (isClosed_iInter (fun x : X => isClosed_le (continuous_norm.comp (continuous_apply x)) continuous_const))
  have hclosed : IsClosed A := (isClosed_setOf_lipschitzWith L).inter hbound
  have hA : IsCompact A :=
    (isCompact_pi_infinite (fun _ : X => isCompact_closedBall (0 : ℂ) B)).of_isClosed_subset hclosed (by
      intro f hf x
      simpa only [Metric.mem_closedBall,dist_zero_right] using hf.2 x)
  have himage : ContinuousMap.toFun '' boundedComplexLipschitzObservables X B L = A := by
    ext f
    constructor
    · rintro ⟨g,hg,rfl⟩
      exact hg
    · intro hf
      exact ⟨⟨f,hf.1.continuous⟩,hf,rfl⟩
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · rwa [himage]
  · apply Metric.equicontinuous_of_continuity_modulus
      (fun t : ℝ => (L : ℝ)*t) (by
        simpa only [mul_zero,id_eq] using (Filter.Tendsto.const_mul (L : ℝ) (Filter.tendsto_id :
          Filter.Tendsto (id : ℝ → ℝ) (nhds 0) (nhds 0))))
    intro x y f
    exact f.property.1.dist_le_mul x y

end Hindman168
