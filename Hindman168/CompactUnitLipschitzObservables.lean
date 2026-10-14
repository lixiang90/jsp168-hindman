import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Complex.Basic

namespace Hindman168
open scoped Topology NNReal

def unitLipschitzObservables (X : Type*) [PseudoMetricSpace X] : Set C(X, ℂ) :=
  {f | LipschitzWith 1 f ∧ ∀ x, ‖f x‖ ≤ 1}

theorem unit_lipschitz_observables_compact (X : Type*) [PseudoMetricSpace X] :
    IsCompact (unitLipschitzObservables X) := by
  let A : Set (X → ℂ) := {f | LipschitzWith 1 f ∧ ∀ x, ‖f x‖ ≤ 1}
  have hbound : IsClosed {f : X → ℂ | ∀ x, ‖f x‖ ≤ 1} := by
    simpa only [Set.setOf_forall, Function.comp_def] using
      (isClosed_iInter (fun x : X => isClosed_le (continuous_norm.comp (continuous_apply x)) continuous_const))
  have hclosed : IsClosed A := (isClosed_setOf_lipschitzWith (1 : ℝ≥0)).inter hbound
  have hA : IsCompact A :=
    (isCompact_pi_infinite (fun _ : X => isCompact_closedBall (0 : ℂ) 1)).of_isClosed_subset hclosed
      (by
        intro f hf x
        simpa only [Metric.mem_closedBall, dist_zero_right] using hf.2 x)
  have himage : ContinuousMap.toFun '' unitLipschitzObservables X = A := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hf
      exact ⟨⟨f, hf.1.continuous⟩, hf, rfl⟩
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · rwa [himage]
  · apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => t) Filter.tendsto_id
    intro x y f
    simpa only [NNReal.coe_one, one_mul] using f.property.1.dist_le_mul x y

end Hindman168
