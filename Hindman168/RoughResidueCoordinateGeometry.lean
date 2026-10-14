import Hindman168.RoughResidueCoordinateEndpoints

namespace Hindman168

theorem rough_residue_coordinate_length_error (A B K u : ℤ) (hK : 0 < K) :
    |(K : ℝ)*((roughResidueCoordinateEndpoint B K u : ℝ)-roughResidueCoordinateEndpoint A K u)-
      ((B : ℝ)-A)| < K := by
  have ha := rough_residue_coordinate_endpoint_bounds A K u hK
  have hb := rough_residue_coordinate_endpoint_bounds B K u hK
  have haR : (A : ℝ) ≤ u+K*(roughResidueCoordinateEndpoint A K u : ℝ) ∧
      (u : ℝ)+K*(roughResidueCoordinateEndpoint A K u : ℝ) < A+K := by exact_mod_cast ha
  have hbR : (B : ℝ) ≤ u+K*(roughResidueCoordinateEndpoint B K u : ℝ) ∧
      (u : ℝ)+K*(roughResidueCoordinateEndpoint B K u : ℝ) < B+K := by exact_mod_cast hb
  apply abs_lt.mpr
  constructor <;> nlinarith

theorem rough_residue_coordinate_length_bounds (A B K u : ℤ) (hK : 0 < K)
    (hlen : 2*K ≤ B-A) :
    ((B : ℝ)-A)/(2*K) ≤ (roughResidueCoordinateEndpoint B K u : ℝ)-roughResidueCoordinateEndpoint A K u ∧
    (roughResidueCoordinateEndpoint B K u : ℝ)-roughResidueCoordinateEndpoint A K u ≤ 2*((B : ℝ)-A)/K := by
  have hp : (0 : ℝ) < K := by exact_mod_cast hK
  have hl : 2*(K : ℝ) ≤ (B : ℝ)-A := by exact_mod_cast hlen
  have hs := abs_lt.mp (rough_residue_coordinate_length_error A B K u hK)
  constructor
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*K)).mpr
    nlinarith
  · apply (le_div_iff₀ hp).mpr
    nlinarith

theorem rough_residue_coordinate_sample_bound (K u y : ℤ) (hK : 0 < K)
    (hu : 0 ≤ u ∧ u < K) (C Z : ℝ) (hx : |((u+K*y : ℤ) : ℝ)| ≤ C*Z) :
    |(y : ℝ)| ≤ C*(Z/K)+1 := by
  have hp : (0 : ℝ) < K := by exact_mod_cast hK
  have huR : (0 : ℝ) ≤ u ∧ (u : ℝ) < K := by exact_mod_cast hu
  have hb := abs_le.mp hx
  push_cast at hb
  have hy' : |(y : ℝ)*(K : ℝ)| ≤ C*Z+K := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hy : |(y : ℝ)| * (K : ℝ) ≤ C*Z+K := by
    simpa only [abs_mul, abs_of_pos hp] using hy'
  have hh := (le_div_iff₀ hp).mpr hy
  apply hh.trans_eq
  field_simp

theorem rough_residue_coordinate_sample_scaled_bound (K u y : ℤ) (hK : 0 < K)
    (hu : 0 ≤ u ∧ u < K) (C Z : ℝ) (hx : |((u+K*y : ℤ) : ℝ)| ≤ C*Z)
    (hscale : 1 ≤ Z/K) : |(y : ℝ)| ≤ (C+1)*(Z/K) := by
  have hh := rough_residue_coordinate_sample_bound K u y hK hu C Z hx
  nlinarith

end Hindman168
