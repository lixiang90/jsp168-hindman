import Hindman168.FiniteSetConditionDomination
import Hindman168.ShortBinPivotLaw

/-! Original harmonic laws conditioned on a dyadic finite set or a complete
dyadic residue bin. Each conditional coefficient is at most twice uniform.
Nonemptiness, cutoff containment and positive normalization are explicit. -/

namespace Hindman168

open FiniteMass
open scoped BigOperators Classical

theorem dyadic_rawMass_bounds {X W : ℕ} {A : ℝ} (hA : 0 < A)
    (hZ : 0 < harmonicNormalizer X W) {S : Finset ℕ}
    (hS : S ⊆ harmonicWindow X W)
    (hdy : ∀ p ∈ S, A ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * A) {p : ℕ} (hp : p ∈ S) :
    (2 * A)⁻¹ / harmonicNormalizer X W ≤ rawMass X W p ∧
      rawMass X W p ≤ 2 * ((2 * A)⁻¹ / harmonicNormalizer X W) := by
  rw [rawMass_apply, harmonicWeight, if_pos (hS hp)]
  constructor
  · apply div_le_div_of_nonneg_right _ hZ.le
    simpa only [one_div] using one_div_le_one_div_of_le
      (hA.trans_le (hdy p hp).1) (hdy p hp).2
  · have hi : (p : ℝ)⁻¹ ≤ A⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hA (hdy p hp).1
    have he : A⁻¹ / harmonicNormalizer X W =
        2 * ((2 * A)⁻¹ / harmonicNormalizer X W) := by field_simp
    rw [← he]
    exact div_le_div_of_nonneg_right hi hZ.le

theorem dyadic_rawMass_event_pos {X W : ℕ} {A : ℝ} (hA : 0 < A)
    (hZ : 0 < harmonicNormalizer X W) {S : Finset ℕ} (hne : S.Nonempty)
    (hS : S ⊆ harmonicWindow X W)
    (hdy : ∀ p ∈ S, A ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * A) :
    0 < event (rawMass X W) (fun p => p ∈ S) :=
  event_finset_mem_pos _ S hne (div_pos (inv_pos.mpr (by positivity)) hZ)
    (fun _ hp => (dyadic_rawMass_bounds hA hZ hS hdy hp).1)

theorem dyadic_harmonic_uniform_bound {X W : ℕ} {A : ℝ} (hA : 0 < A)
    (hZ : 0 < harmonicNormalizer X W) {S : Finset ℕ} (hne : S.Nonempty)
    (hS : S ⊆ harmonicWindow X W)
    (hdy : ∀ p ∈ S, A ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * A) (p : ℕ) :
    conditionMass (rawMass X W) (fun p => p ∈ S) p ≤ 2 * uniformFinsetMass S p :=
  conditionMass_finset_uniform_bound _ S hne
    (div_pos (inv_pos.mpr (by positivity)) hZ) (by norm_num)
    (fun _ hp => (dyadic_rawMass_bounds hA hZ hS hdy hp).1)
    (fun _ hp => (dyadic_rawMass_bounds hA hZ hS hdy hp).2) p

theorem dyadic_residueWindow_subset {X W L r : ℕ} {A : ℝ}
    (hlo : (X : ℝ) ≤ A) (hhi : 2 * A ≤ (X ^ 2 : ℕ))
    (hWL : W ∣ L) (hr : r.Coprime W) :
    residueWindow A (2 * A) L r ⊆ harmonicWindow X W := by
  intro p hp
  obtain ⟨hp, hp', hres⟩ := mem_residueWindow.mp hp
  have hl : X ≤ p := by exact_mod_cast hlo.trans hp
  have hh : p < X ^ 2 := by exact_mod_cast hp'.trans_le hhi
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hl, hh⟩,
    (residue_coprime_iff W L r p hWL hres).mpr hr⟩

theorem dyadic_residue_harmonic_uniform_bound {X W L r : ℕ} {A : ℝ}
    (hA : 0 < A) (hZ : 0 < harmonicNormalizer X W)
    (hne : (residueWindow A (2 * A) L r).Nonempty)
    (hlo : (X : ℝ) ≤ A) (hhi : 2 * A ≤ (X ^ 2 : ℕ))
    (hWL : W ∣ L) (hr : r.Coprime W) (p : ℕ) :
    conditionMass (rawMass X W) (fun p => p ∈ residueWindow A (2 * A) L r) p ≤
      2 * uniformFinsetMass (residueWindow A (2 * A) L r) p :=
  dyadic_harmonic_uniform_bound hA hZ hne (dyadic_residueWindow_subset hlo hhi hWL hr)
    (fun _ hp => ⟨(mem_residueWindow.mp hp).1, (mem_residueWindow.mp hp).2.1.le⟩) p

end Hindman168
