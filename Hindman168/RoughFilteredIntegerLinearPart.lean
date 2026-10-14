import Hindman168.RoughFilteredPolynomialTranslation
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The actual normalized integer sequence is linear modulo its second
filtration layer. No commutativity or normality of the original lattice
is used; only the stated normal filtration layer is quotiented. -/

namespace Hindman168
variable {G : Type*} [Group G]

theorem integer_sequence_eq_zpow_of_second_difference (P : ℤ → G)
    (h0 : P 0 = 1)
    (h2 : ∀ n : ℤ, roughIteratedGroupDifference P [n,1] 0 = 1) :
    ∀ n : ℤ, P n = P 1 ^ n := by
  have hstep : ∀ n : ℤ, P (n+1) = P 1 * P n := by
    intro n
    have h := h2 n
    simp only [roughIteratedGroupDifference,roughGroupDifference,zero_add,h0,
      inv_one,mul_one] at h
    have he : P (n+1) * (P n)⁻¹ = P 1 := mul_inv_eq_one.mp h
    exact (mul_inv_eq_iff_eq_mul.mp he)
  intro n
  induction n using Int.induction_on with
  | zero => simpa only [zpow_zero] using h0
  | succ n ih =>
      rw [hstep,ih]
      calc
        P 1 * P 1 ^ (n : ℤ) = P 1 ^ (1 : ℤ) * P 1 ^ (n : ℤ) := by
          rw [zpow_one]
        _ = P 1 ^ (1+(n : ℤ)) := (zpow_add _ _ _).symm
        _ = P 1 ^ ((n : ℤ)+1) := by congr 1; omega
  | pred n ih =>
      have h := hstep (-(n : ℤ)-1)
      rw [show -(n : ℤ)-1+1 = -(n : ℤ) by omega,ih] at h
      calc
        P (-(n : ℤ)-1) = (P 1)⁻¹ * (P 1 * P (-(n : ℤ)-1)) :=
          (inv_mul_cancel_left _ _).symm
        _ = (P 1)⁻¹ * (P 1 ^ (-(n : ℤ))) := congrArg (fun x => (P 1)⁻¹*x) h.symm
        _ = P 1 ^ (-(n : ℤ)-1) := by
          rw [← zpow_neg_one,← zpow_add]
          congr 1
          omega

theorem rough_iterated_group_difference_hom (P : ℤ → G)
    {H : Type*} [Group H] (φ : G →* H) (hs : List ℤ) (x : ℤ) :
    roughIteratedGroupDifference (fun n => φ (P n)) hs x =
      φ (roughIteratedGroupDifference P hs x) := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih =>
      simp only [roughIteratedGroupDifference,roughGroupDifference,ih,map_mul,map_inv]

theorem rough_filtered_integer_nonlinear_part_mem (F : ℕ → Subgroup G)
    [(F 2).Normal] (P : ℤ → G) (hP : RoughFilteredPolynomial F P)
    (h0 : P 0 = 1) (n : ℤ) : P n * (P 1 ^ n)⁻¹ ∈ F 2 := by
  let φ : G →* G ⧸ F 2 := QuotientGroup.mk' (F 2)
  have he : ∀ n : ℤ, φ (P n) = φ (P 1) ^ n := by
    apply integer_sequence_eq_zpow_of_second_difference
    · rw [h0,map_one]
    · intro m
      rw [rough_iterated_group_difference_hom]
      exact (QuotientGroup.eq_one_iff _).mpr (hP [m,1] 0)
  apply (QuotientGroup.eq_one_iff _).mp
  change φ (P n * (P 1 ^ n)⁻¹) = 1
  rw [map_mul,map_inv,map_zpow,he,mul_inv_cancel]

end Hindman168
