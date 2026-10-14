import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Lipschitz
import Hindman168.RoughScaledMonomials
import Mathlib.Tactic

namespace Hindman168
open Set

theorem rough_compact_parameter_modulus {X Y : Type*}
    [PseudoMetricSpace X] [CompactSpace X] [PseudoMetricSpace Y]
    (f : ℝ × X → Y) (hf : Continuous f) (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (t u : ℝ) (x : X),
      |t| ≤ B → |u| ≤ B → |t - u| ≤ δ → dist (f (t, x)) (f (u, x)) ≤ ε := by
  have hc : IsCompact (Icc (-B) B ×ˢ (univ : Set X)) := isCompact_Icc.prod isCompact_univ
  obtain ⟨δ, hδ, hm⟩ := Metric.uniformContinuousOn_iff_le.mp
    (hc.uniformContinuousOn_of_continuous hf.continuousOn) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro t u x ht hu htu
  apply hm (t, x) ⟨abs_le.mp ht, mem_univ _⟩ (u, x) ⟨abs_le.mp hu, mem_univ _⟩
  simp only [Prod.dist_eq, Real.dist_eq, dist_self]
  exact max_le htu hδ.le

theorem rough_compact_lipschitz_test_freezing {X Y : Type*}
    [PseudoMetricSpace X] [CompactSpace X] [PseudoMetricSpace Y]
    (f : ℝ × X → Y) (hf : Continuous f) (B K : ℝ) (hK : 0 ≤ K)
    (L : NNReal) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ (F : Y → ℝ), LipschitzWith L F →
      ∀ (t u : ℝ) (x : X), |t| ≤ B → |u| ≤ B → |t - u| ≤ K * r →
        |F (f (t, x)) - F (f (u, x))| < ε := by
  have hLp : 0 < (L : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ, hm⟩ := rough_compact_parameter_modulus f hf B (div_pos hε hLp)
  refine ⟨δ / (K + 1), div_pos hδ (by positivity), ?_⟩
  intro F hF t u x ht hu htu
  have hsmall : K * (δ / (K + 1)) ≤ δ := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < K + 1)).mpr
    nlinarith
  have hdist := hm t u x ht hu (htu.trans hsmall)
  have hbound : |F (f (t, x)) - F (f (u, x))| ≤ (L : ℝ) * (ε / ((L : ℝ) + 1)) :=
    (hF.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)
  apply hbound.trans_lt
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hLp).mpr
  nlinarith

end Hindman168
