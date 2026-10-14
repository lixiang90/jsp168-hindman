import Hindman168.RoughResidueIndexRange

/-! Natural positive-step parametrization of the exact original residue
interval. Signed index endpoints need not themselves be nonnegative. -/
namespace Hindman168
open scoped Classical

theorem rough_natural_residue_index_range_image (A B r : ℤ) (K : ℕ)
    (hK : 0 < K) (hA : 0 ≤ A) :
    (Finset.range ((roughResidueCoordinateEndpoint B K r-
      roughResidueCoordinateEndpoint A K r).toNat)).image
      (fun n : ℕ => (alignmentResidueEndpoint A K r).toNat+K*n) =
      (alignmentIntervalClass A B K r).image Int.toNat := by
  have hKZ : (0 : ℤ) < K := by exact_mod_cast hK
  have hstart : 0 ≤ alignmentResidueEndpoint A K r :=
    hA.trans (alignmentResidueEndpoint_bounds A K r hKZ).1
  rw [← rough_residue_index_range_image A B K r hKZ,Finset.image_image]
  apply Finset.image_congr
  intro n _hn
  dsimp only [Function.comp_apply]
  apply Int.ofNat_inj.mp
  rw [Nat.cast_add,Nat.cast_mul,Int.natCast_toNat_eq_self.mpr hstart,
    Int.natCast_toNat_eq_self.mpr (add_nonneg hstart (mul_nonneg hKZ.le (Int.natCast_nonneg n)))]

theorem rough_natural_residue_index_range_card (A B r : ℤ) (K : ℕ)
    (hK : 0 < K) (hA : 0 ≤ A) :
    ((alignmentIntervalClass A B K r).image Int.toNat).card =
      (roughResidueCoordinateEndpoint B K r-roughResidueCoordinateEndpoint A K r).toNat := by
  have hinj : Function.Injective (fun n : ℕ => (alignmentResidueEndpoint A K r).toNat+K*n) := by
    intro n m he
    exact Nat.eq_of_mul_eq_mul_left hK (Nat.add_left_cancel he)
  rw [← rough_natural_residue_index_range_image A B r K hK hA,
    Finset.card_image_of_injective _ hinj,Finset.card_range]

end Hindman168
