import Hindman168.RoughFilteredIntegerLinearPart
import Hindman168.RelativeSquareSubgroup

/-! The actual Green-Tao normalized shifted pair belongs to the relative
square. This proves group membership and exact translated sample identities;
its full relative filtered polynomial degree is a separate assertion. -/

namespace Hindman168
open scoped commutatorElement
variable {G : Type*} [Group G]

def roughNormalizedIntegerPair (P : ℤ → G) (r : G) (h n : ℤ) : G × G :=
  (r⁻¹ * (P (n+h) * (P 1 ^ (n+h))⁻¹) * P 1 ^ n * r,
    (P n * (P 1 ^ n)⁻¹) * P 1 ^ n)

theorem rough_normalized_integer_pair_second (P : ℤ → G) (r : G) (h n : ℤ) :
    (roughNormalizedIntegerPair P r h n).2 = P n := by
  simp only [roughNormalizedIntegerPair,mul_assoc,inv_mul_cancel,mul_one]

theorem rough_normalized_integer_pair_translated_first (P : ℤ → G) (r : G) (h n : ℤ) :
    r * (roughNormalizedIntegerPair P r h n).1 = P (n+h) * (P 1 ^ h)⁻¹ * r := by
  simp only [roughNormalizedIntegerPair,zpow_add,mul_inv_rev]
  simp only [mul_assoc,mul_inv_cancel_left,inv_mul_cancel_left]

theorem rough_normalized_integer_pair_original_coset (Γ : Subgroup G)
    (P : ℤ → G) (r : G) (h n : ℤ) (γ : Γ) (hr : P 1 ^ h = r * γ) :
    (QuotientGroup.mk (r * (roughNormalizedIntegerPair P r h n).1) : G ⧸ Γ) =
      QuotientGroup.mk (P (n+h)) := by
  rw [rough_normalized_integer_pair_translated_first,hr,mul_inv_rev]
  simp only [mul_assoc,inv_mul_cancel,mul_one]
  exact QuotientGroup.mk_mul_of_mem _ (Γ.inv_mem γ.property)

theorem rough_normalized_integer_pair_mem (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (h1 : F 1 = ⊤) [(F 2).Normal]
    (P : ℤ → G) (hP : RoughFilteredPolynomial F P) (h0 : P 0 = 1)
    (r : G) (h n : ℤ) :
    roughNormalizedIntegerPair P r h n ∈ relativeSquareSubgroup (F 1) (F 2) := by
  let φ : G →* G ⧸ F 2 := QuotientGroup.mk' (F 2)
  have hNL : ∀ m : ℤ, φ (P m * (P 1 ^ m)⁻¹) = 1 := by
    intro m
    exact (QuotientGroup.eq_one_iff _).mpr
      (rough_filtered_integer_nonlinear_part_mem F P hP h0 m)
  have hLinear : φ (P n) = φ (P 1 ^ n) := by
    have h := hNL n
    rw [map_mul,map_inv] at h
    exact mul_inv_eq_one.mp h
  have hcomm : φ (P 1 ^ n) * φ r = φ r * φ (P 1 ^ n) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply hF.commutator_mem 1 1
    · rw [h1]; exact Subgroup.mem_top _
    · rw [h1]; exact Subgroup.mem_top _
  apply (relative_square_mem_iff _ _ _).mpr
  refine ⟨?_,?_,?_⟩
  · rw [h1]; exact Subgroup.mem_top _
  · rw [h1]; exact Subgroup.mem_top _
  · apply (QuotientGroup.eq_one_iff _).mp
    change φ ((roughNormalizedIntegerPair P r h n).2⁻¹ * (roughNormalizedIntegerPair P r h n).1) = 1
    rw [map_mul,map_inv,rough_normalized_integer_pair_second]
    change (φ (P n))⁻¹ * φ (r⁻¹ * (P (n+h) * (P 1 ^ (n+h))⁻¹) * P 1 ^ n * r) = 1
    simp only [map_mul,map_inv,hNL,mul_one]
    rw [mul_assoc (φ r)⁻¹,hcomm,hLinear]
    simp only [← mul_assoc,inv_mul_cancel,one_mul]

end Hindman168
