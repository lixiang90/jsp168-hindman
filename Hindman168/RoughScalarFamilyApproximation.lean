import Hindman168.RoughCompactFamilyApproximation

namespace Hindman168
open Set

theorem rough_scalar_family_lipschitz_approximation {X Y : Type*}
    [PseudoMetricSpace X] [CompactSpace X] [Nonempty X] [PseudoMetricSpace Y]
    (φ : ℝ × X → Y) (hφ : Continuous φ) (R B : ℝ) (hB : 0 ≤ B)
    (L : NNReal) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : NNReal, ∀ (t : ℝ), |t| ≤ R → ∀ (F : Y → ℝ), LipschitzWith L F →
      (∀ y, |F y| ≤ B) → ∃ g : X → ℝ, LipschitzWith K g ∧
        (∀ x, |F (φ (t, x)) - g x| ≤ ε) ∧ (∀ x, |g x| ≤ B) := by
  letI : CompactSpace (Icc (-R) R) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hc : Continuous (fun p : Icc (-R) R × X => φ (p.1.val, p.2)) :=
    hφ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨K, hK⟩ := rough_compact_family_lipschitz_approximation _ hc B hB L hε
  exact ⟨K, fun t ht F hF hb => hK ⟨t, abs_le.mp ht⟩ F hF hb⟩

end Hindman168
