import Hindman168.AlignedInteriorMassBound
import Hindman168.NilBoundaryMasterRates

namespace Hindman168
open scoped BigOperators

theorem harmonicNormalizer_reciprocal_le_modulus {X W : ℕ} (hX : 2 ≤ X) (hW : 0 < W)
    (hlog : 2 ≤ Real.log (X : ℝ)) (hWX : (W : ℝ) / X ≤ 1) :
    1 / harmonicNormalizer X W ≤ (W : ℝ) := by
  obtain ⟨hz, hu, _⟩ := harmonicNormalizer_boundary_lower hX hW hlog hWX
  have hw : (0 : ℝ) < W := by exact_mod_cast hW
  have ht : (1 : ℝ) ≤ W.totient := by exact_mod_cast Nat.succ_le_of_lt (Nat.totient_pos.mpr hW)
  have he : (W : ℝ) * unitDensity W = W.totient := by
    unfold unitDensity
    field_simp
  have hm := mul_le_mul_of_nonneg_left hu hw.le
  rw [he] at hm
  exact (div_le_iff₀ hz).mpr (ht.trans hm)

theorem alignedInterior_deleted_integerMass_crude {X W R : ℕ} (hX : 2 ≤ X)
    (hW : 0 < W) (hR : 0 < R) (hlog : 2 ≤ Real.log (X : ℝ))
    (hWX : (W : ℝ) / X ≤ 1) :
    (∑ y ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℕ) \
      Finset.Ico (((X : ℤ) / R + 1) * R) (((X ^ 2 : ℕ) : ℤ) / R * R),
      integerMass X W y) ≤ 2 * ((W : ℝ) * ((R : ℝ) + 1) / X) := by
  have hx : 0 < X := by omega
  have hz := (harmonicNormalizer_boundary_lower hX hW hlog hWX).1
  have hi := harmonicNormalizer_reciprocal_le_modulus hX hW hlog hWX
  have hm := mul_le_mul_of_nonneg_left hi (by positivity : (0 : ℝ) ≤ (2 * R : ℕ) / X)
  have he : (2 * R : ℕ) * ((1 / (X : ℝ)) / harmonicNormalizer X W) ≤
      2 * (W : ℝ) * R / X := by
    calc
      _ = ((2 * R : ℕ) : ℝ) / X * (1 / harmonicNormalizer X W) := by ring
      _ ≤ ((2 * R : ℕ) : ℝ) / X * W := hm
      _ = _ := by push_cast; ring
  refine (alignedInterior_deleted_integerMass_le X W R hx hR hz).trans (he.trans ?_)
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg X)
  nlinarith [Nat.cast_nonneg (α := ℝ) W]

end Hindman168
