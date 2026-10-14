import Hindman168.PositivePrincipalSumPivotConditioning
import Hindman168.HarmonicTranslation

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

/-- The §8.5 shift-removal step for the original harmonic integer law.
The displacement may depend on every earlier raw variable. -/
theorem principal_harmonic_pivot_extension {α V : Type*} [Fintype V] [Nonempty V]
    (μ : Mass α) (E G : α → Prop) (P : α → ℤ → Prop)
    (X W : ℕ) (s : V → α → ℤ) (H c : ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hX : 2 ≤ X) (hW : 0 < W)
    (hlog : (W : ℝ) / X < Real.log X) (hH : 0 ≤ H) (hc : 0 ≤ c)
    (hs : ∀ v x, x ∈ μ.support → (W : ℤ) ∣ s v x ∧ |(s v x : ℝ)| ≤ H)
    (hgood : ∀ x ∈ μ.support, G x →
      c ≤ ∑ v, event (integerMass X W) (fun p => P x (p + s v x))) :
    (c / Fintype.card V) * event μ E -
      (c / Fintype.card V) * event μ (fun x => ¬ G x) -
      (2 * H / ((X : ℝ) * (Real.log X - (W : ℝ) / X))) * total μ ≤
      event (conditionalJoint μ (fun _ => integerMass X W))
        (fun xp => E xp.1 ∧ P xp.1 xp.2) := by
  have hd : 0 ≤ (X : ℝ) * (Real.log X - (W : ℝ) / X) :=
    mul_nonneg (Nat.cast_nonneg _) (sub_pos.mpr hlog).le
  apply principal_slot_removal μ (fun _ => integerMass X W)
    (fun v x => (integerMass X W).mapDomain (fun p => p + s v x)) E G P hμ
    (fun _ => integerMass_nonneg (harmonicNormalizer_pos hX hW hlog)) c _ hc
    (div_nonneg (mul_nonneg (by norm_num) hH) hd)
  · simpa only [event_map] using hgood
  · intro v x hx
    exact ((integer_harmonic_translation_error hX hW hlog (hs v x hx).1).trans
      (min_le_right _ _)).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hs v x hx).2 (by norm_num)) hd)
end Hindman168
