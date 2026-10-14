import Hindman168.RoughResidueBoxTransport
import Hindman168.RoughResidueCoordinateGeometry

namespace Hindman168
open scoped Classical

theorem rough_residue_box_scaled_side_bounds {ι : Type*}
    (A B u : ι → ℤ) (K : ℤ) (hK : 0 < K) (hlen : ∀ j, 2*K ≤ B j-A j)
    (c C Z : ℝ) (hlo : ∀ j, c*Z ≤ (B j : ℝ)-A j)
    (hhi : ∀ j, (B j : ℝ)-A j ≤ C*Z) :
    ∀ j, (c/2)*(Z/K) ≤ (roughResidueBoxEndpoint B u K j : ℝ)-roughResidueBoxEndpoint A u K j ∧
      (roughResidueBoxEndpoint B u K j : ℝ)-roughResidueBoxEndpoint A u K j ≤ (2*C)*(Z/K) := by
  have hp : (0 : ℝ) < K := by exact_mod_cast hK
  intro j
  have hs := rough_residue_coordinate_length_bounds (A j) (B j) K (u j) hK (hlen j)
  constructor
  · calc
      _ = c*Z/(2*K) := by ring
      _ ≤ ((B j : ℝ)-A j)/(2*K) := div_le_div_of_nonneg_right (hlo j) (by positivity)
      _ ≤ _ := hs.1
  · calc
      _ ≤ 2*((B j : ℝ)-A j)/K := hs.2
      _ ≤ 2*(C*Z)/K := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hhi j) (by norm_num : (0:ℝ) ≤ 2)) hp.le
      _ = _ := by ring

theorem rough_residue_box_position_bound {ι : Type*} [Fintype ι]
    (A B u : ι → ℤ) (K : ℤ) (hK : 0 < K) (hu : ∀ j, 0 ≤ u j ∧ u j < K)
    (C Z : ℝ) (hscale : 1 ≤ Z/K) (hA : ∀ j, |(A j : ℝ)| ≤ C*Z)
    (hB : ∀ j, |(B j : ℝ)| ≤ C*Z) (y : ι → ℤ)
    (hy : y ∈ Fintype.piFinset (fun j =>
      Finset.Ico (roughResidueBoxEndpoint A u K j) (roughResidueBoxEndpoint B u K j))) :
    ∀ j, |(y j : ℝ)| ≤ (C+1)*(Z/K) := by
  have hx : roughResidueBoxAffine u K y ∈ alignmentBoxClass A B u K := by
    rw [← rough_residue_box_unrestricted_image A B u K hK]
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  intro j
  apply rough_residue_coordinate_sample_scaled_bound K (u j) (y j) hK (hu j) C Z _ hscale
  have hi := Finset.mem_Ico.mp (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hx j)).1
  have hiR : (A j : ℝ) ≤ ((roughResidueBoxAffine u K y j : ℤ) : ℝ) ∧
      ((roughResidueBoxAffine u K y j : ℤ) : ℝ) < B j := by exact_mod_cast hi
  change (A j : ℝ) ≤ ((u j + K*y j : ℤ) : ℝ) ∧
    ((u j + K*y j : ℤ) : ℝ) < B j at hiR
  have ha := abs_le.mp (hA j)
  have hb := abs_le.mp (hB j)
  apply abs_le.mpr
  constructor <;> linarith

end Hindman168
