import Hindman168.RoughFilteredPolynomialTranslation
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Group

/-! Actual original basepoint normalization preserves the original normal
filtration and original nonnormal lattice coset samples after a true
basepoint representative factorization. -/

namespace Hindman168
variable {V G : Type*} [AddCommMonoid V] [Group G]

def roughGroupBasepointNormalization (P : V → G) (r : G) (x : V) : G :=
  r⁻¹ * P x * (P 0)⁻¹ * r

theorem rough_group_basepoint_normalization_zero (P : V → G) (r : G) :
    roughGroupBasepointNormalization P r 0 = 1 := by
  simp only [roughGroupBasepointNormalization,mul_assoc,mul_inv_cancel_left,inv_mul_cancel]

theorem rough_group_basepoint_normalization_original_coset (Γ : Subgroup G)
    (P : V → G) (r : G) (γ : Γ) (hr : P 0 = r * γ) (x : V) :
    (QuotientGroup.mk (r * roughGroupBasepointNormalization P r x) : G ⧸ Γ) =
      QuotientGroup.mk (P x) := by
  simp only [roughGroupBasepointNormalization,hr,mul_inv_rev,mul_assoc,
    mul_inv_cancel_left,inv_mul_cancel,mul_one]
  exact QuotientGroup.mk_mul_of_mem _ (Γ.inv_mem γ.property)

theorem rough_group_basepoint_normalization_difference (P : V → G) (r : G) (h x : V) :
    roughGroupDifference (roughGroupBasepointNormalization P r) h x =
      r⁻¹ * roughGroupDifference P h x * r := by
  simp only [roughGroupDifference,roughGroupBasepointNormalization,mul_inv_rev,inv_inv]
  group

theorem rough_iterated_group_difference_conjugate (P : V → G) (r : G) (hs : List V) (x : V) :
    roughIteratedGroupDifference (fun y => r⁻¹*P y*r) hs x =
      r⁻¹ * roughIteratedGroupDifference P hs x * r := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih =>
      simp only [roughIteratedGroupDifference,roughGroupDifference,ih,mul_inv_rev,inv_inv]
      group

theorem rough_group_basepoint_normalization_iterated_difference (P : V → G) (r : G)
    (hs : List V) (hne : hs ≠ []) (x : V) :
    roughIteratedGroupDifference (roughGroupBasepointNormalization P r) hs x =
      r⁻¹ * roughIteratedGroupDifference P hs x * r := by
  induction hs generalizing x with
  | nil => exact False.elim (hne rfl)
  | cons h hs ih =>
      cases hs with
      | nil => exact rough_group_basepoint_normalization_difference P r h x
      | cons k ks =>
          change roughGroupDifference
            (roughIteratedGroupDifference (roughGroupBasepointNormalization P r) (k::ks)) h x = _
          have he : roughIteratedGroupDifference (roughGroupBasepointNormalization P r) (k::ks) =
              fun y => r⁻¹ * roughIteratedGroupDifference P (k::ks) y * r :=
            funext (ih (by simp only [ne_eq,List.cons_ne_nil,not_false_eq_true]))
          rw [he]
          simp only [roughGroupDifference,roughIteratedGroupDifference,mul_inv_rev,inv_inv]
          group

theorem rough_group_basepoint_normalization_filtered (F : ℕ → Subgroup G)
    (h0 : F 0 = ⊤) (hN : ∀ i, (F i).Normal)
    (P : V → G) (hP : RoughFilteredPolynomial F P) (r : G) :
    RoughFilteredPolynomial F (roughGroupBasepointNormalization P r) := by
  intro hs x
  by_cases he : hs = []
  · subst hs
    rw [List.length_nil,h0]
    exact Subgroup.mem_top _
  · rw [rough_group_basepoint_normalization_iterated_difference P r hs he]
    simpa only [inv_inv] using (hN hs.length).conj_mem _ (hP hs x) r⁻¹

end Hindman168
