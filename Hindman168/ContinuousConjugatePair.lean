import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Complex.Basic

/-! Actual continuous paired observables with conjugation, uniform norm
bound and genuine compact-family continuity. -/

namespace Hindman168
variable {X : Type*} [TopologicalSpace X]

noncomputable def continuousConjugatePair (F G : C(X, ℂ)) : C(X × X, ℂ) :=
  ⟨fun p => F p.1 * star (G p.2),
    (F.continuous.comp continuous_fst).mul
      (continuous_star.comp (G.continuous.comp continuous_snd))⟩

theorem continuous_conjugate_pair_apply (F G : C(X, ℂ)) (q r : X) :
    continuousConjugatePair F G (q,r) = F q * star (G r) := rfl

variable [CompactSpace X]

theorem continuous_conjugate_pair_norm (F G : C(X, ℂ)) :
    ‖continuousConjugatePair F G‖ ≤ ‖F‖*‖G‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg F) (norm_nonneg G))).mpr
  intro p
  change ‖F p.1 * star (G p.2)‖ ≤ _
  rw [norm_mul,norm_star]
  exact mul_le_mul (F.norm_coe_le_norm p.1) (G.norm_coe_le_norm p.2) (norm_nonneg _) (norm_nonneg _)

theorem continuous_conjugate_pair_continuous :
    Continuous (fun p : C(X, ℂ) × C(X, ℂ) => continuousConjugatePair p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hF : Continuous (fun p : (C(X, ℂ) × C(X, ℂ)) × (X × X) => p.1.1 p.2.1) :=
    continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd.fst)
  have hG : Continuous (fun p : (C(X, ℂ) × C(X, ℂ)) × (X × X) => p.1.2 p.2.2) :=
    continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd.snd)
  exact hF.mul hG.star

theorem continuous_conjugate_self_family_compact (H : Set C(X, ℂ)) (hH : IsCompact H) :
    IsCompact ((fun F => continuousConjugatePair F F) '' H) :=
  hH.image (continuous_conjugate_pair_continuous.comp (continuous_id.prodMk continuous_id))

end Hindman168
