import Hindman168.AlignmentRetainedClassMean

namespace Hindman168

theorem alignmentRetainedEndpoint_error (L D a : ℤ) (hD : 0 < D)
    (ha : 0 ≤ a) (haD : a < D) :
    |D * alignmentRetainedEndpoint L D a - L| < D := by
  have h := alignmentResidueEndpoint_bounds L D a hD
  have hr := alignmentRetainedEndpoint_reconstruct L D a
  rw [abs_lt]
  omega

theorem alignmentRetainedEndpoint_side_error (L U D a : ℤ) (hD : 0 < D) :
    |D * (alignmentRetainedEndpoint U D a - alignmentRetainedEndpoint L D a) - (U - L)| < D := by
  have hl := alignmentResidueEndpoint_bounds L D a hD
  have hu := alignmentResidueEndpoint_bounds U D a hD
  have hrl := alignmentRetainedEndpoint_reconstruct L D a
  have hru := alignmentRetainedEndpoint_reconstruct U D a
  rw [abs_lt]
  constructor <;> nlinarith

theorem alignmentRetainedEndpoint_location (L D a : ℤ) (Z C : ℝ) (hD : 0 < D)
    (ha : 0 ≤ a) (haD : a < D) (hL : |(L : ℝ)| ≤ C * Z) (hDZ : (D : ℝ) ≤ Z) :
    |(alignmentRetainedEndpoint L D a : ℝ)| ≤ (C + 1) * (Z / D) := by
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  have he : |(D : ℝ) * alignmentRetainedEndpoint L D a - L| < D := by
    exact_mod_cast alignmentRetainedEndpoint_error L D a hD ha haD
  have hb := abs_add_le ((D : ℝ) * alignmentRetainedEndpoint L D a - L) (L : ℝ)
  have hm : (D : ℝ) * |(alignmentRetainedEndpoint L D a : ℝ)| ≤ (C + 1) * Z := by
    rw [sub_add_cancel, abs_mul, abs_of_pos hd] at hb
    linarith
  rw [← mul_div_assoc, le_div_iff₀ hd]
  nlinarith

theorem alignmentRetainedEndpoint_sides (L U D a : ℤ) (Z c C : ℝ) (hD : 0 < D)
    (hlo : c * Z ≤ (U : ℝ) - L) (hhi : (U : ℝ) - L ≤ C * Z)
    (hDc : (D : ℝ) ≤ (c / 2) * Z) (hDZ : (D : ℝ) ≤ Z) :
    (c / 2) * (Z / D) ≤
        (alignmentRetainedEndpoint U D a : ℝ) - alignmentRetainedEndpoint L D a ∧
      (alignmentRetainedEndpoint U D a : ℝ) - alignmentRetainedEndpoint L D a ≤
        (C + 1) * (Z / D) := by
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  have he : |(D : ℝ) * ((alignmentRetainedEndpoint U D a : ℝ) -
      alignmentRetainedEndpoint L D a) - ((U : ℝ) - L)| < D := by
    exact_mod_cast alignmentRetainedEndpoint_side_error L U D a hD
  rw [abs_lt] at he
  constructor
  · rw [← mul_div_assoc, div_le_iff₀ hd]
    nlinarith [he.1]
  · rw [← mul_div_assoc, le_div_iff₀ hd]
    nlinarith [he.2]

end Hindman168
