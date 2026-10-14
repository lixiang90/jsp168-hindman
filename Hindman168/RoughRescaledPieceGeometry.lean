import Hindman168.RoughBalancedBoxGeometry
import Hindman168.RoughResidueBoxGeometry

namespace Hindman168
open scoped Classical

theorem rough_residue_endpoint_scaled_bound (A K u : ℤ) (hK : 0 < K)
    (hu : 0 ≤ u ∧ u < K) (C Z : ℝ) (hA : |(A : ℝ)| ≤ C*Z)
    (hscale : 1 ≤ Z/K) :
    |(roughResidueCoordinateEndpoint A K u : ℝ)| ≤ (C+1)*(Z/K) := by
  have hp : (0 : ℝ) < K := by exact_mod_cast hK
  have huR : (0 : ℝ) ≤ u ∧ (u : ℝ) < K := by exact_mod_cast hu
  have he := rough_residue_coordinate_endpoint_bounds A K u hK
  have heR : (A : ℝ) ≤ u+K*(roughResidueCoordinateEndpoint A K u : ℝ) ∧
      (u : ℝ)+K*(roughResidueCoordinateEndpoint A K u : ℝ) < A+K := by
    exact_mod_cast he
  have ha := abs_le.mp hA
  have hb : |(roughResidueCoordinateEndpoint A K u : ℝ)| * K ≤ C*Z+K := by
    have hh : |(roughResidueCoordinateEndpoint A K u : ℝ) * K| ≤ C*Z+K :=
      abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    simpa only [abs_mul, abs_of_pos hp] using hh
  have hh := (le_div_iff₀ hp).mpr hb
  have hid : (C*Z+K)/K = C*(Z/K)+1 := by field_simp
  rw [hid] at hh
  nlinarith

theorem rough_rescaled_piece_geometry {ι : Type*}
    (A B : ι → ℤ) (N K : ℕ) (hN : 0 < N) (hK : 0 < K)
    (hlen : ∀ j, (2*N*K : ℤ) ≤ B j-A j)
    (c C Z : ℝ) (hlo : ∀ j, c*Z ≤ (B j : ℝ)-A j)
    (hhi : ∀ j, (B j : ℝ)-A j ≤ C*Z)
    (hA : ∀ j, |(A j : ℝ)| ≤ C*Z) (hB : ∀ j, |(B j : ℝ)| ≤ C*Z)
    (hscale : 1 ≤ Z/K) (p : (ι → Fin N) × (ι → Fin K)) :
    let u : ι → ℤ := fun j => (p.2 j).val
    let l := roughResidueBoxEndpoint (roughBoxLower A B N p.1) u K
    let r := roughResidueBoxEndpoint (roughBoxUpper A B N p.1) u K
    ∀ j, (c/(4*N))*(Z/K) ≤ (r j : ℝ)-l j ∧
      (r j : ℝ)-l j ≤ (4*C/N)*(Z/K) ∧
      |(l j : ℝ)| ≤ (C+1)*(Z/K) ∧ |(r j : ℝ)| ≤ (C+1)*(Z/K) := by
  intro u l r
  have hn : (0 : ℤ) < N := by exact_mod_cast hN
  have hk : (0 : ℤ) < K := by exact_mod_cast hK
  have hk1 : (1 : ℤ) ≤ K := by omega
  have hnlen : ∀ j, 2*(N : ℤ) ≤ B j-A j := fun j => by nlinarith [hlen j]
  have hab : ∀ j, A j ≤ B j := fun j => by have hh := hnlen j; omega
  have hpiece : ∀ j, 2*(K : ℤ) ≤ roughBoxUpper A B N p.1 j-roughBoxLower A B N p.1 j := by
    intro j
    have hnat : 2*K ≤ (B j-A j).toNat/N := by
      apply (Nat.le_div_iff_mul_le hN).mpr
      have hh : (2*N*K : ℤ) ≤ B j-A j := hlen j
      have hhZ : ((2*N*K : ℕ) : ℤ) ≤ B j-A j := by
        push_cast
        exact hh
      have hh' : (2*N*K : ℕ) ≤ (B j-A j).toNat := by omega
      nlinarith
    have hh : (2*K : ℤ) ≤ ((B j-A j).toNat/N : ℕ) := by exact_mod_cast hnat
    exact hh.trans (rough_balanced_cut_step (A j) (B j) N (p.1 j).val).1
  have hs := rough_balanced_box_scaled_sides A B N hN hnlen c C Z hlo hhi p.1
  have hs' := rough_residue_box_scaled_side_bounds _ _ u K hk hpiece (c/(2*N)) (2*C/N) Z
    (fun j => by convert (hs j).1 using 1; ring)
    (fun j => by convert (hs j).2 using 1; ring)
  simp only [Int.cast_natCast] at hs'
  have hc := rough_balanced_box_contained A B N hN hab p.1
  have hpos : ∀ j, |(roughBoxLower A B N p.1 j : ℝ)| ≤ C*Z ∧
      |(roughBoxUpper A B N p.1 j : ℝ)| ≤ C*Z := by
    intro j
    have hl : (A j : ℝ) ≤ roughBoxLower A B N p.1 j := by exact_mod_cast hc.1 j
    have hm : (roughBoxLower A B N p.1 j : ℝ) ≤ roughBoxUpper A B N p.1 j := by exact_mod_cast hc.2.1 j
    have hr : (roughBoxUpper A B N p.1 j : ℝ) ≤ B j := by exact_mod_cast hc.2.2 j
    have ha := abs_le.mp (hA j)
    have hb := abs_le.mp (hB j)
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  intro j
  have hu : 0 ≤ u j ∧ u j < (K : ℤ) := by
    change 0 ≤ ((p.2 j).val : ℤ) ∧ ((p.2 j).val : ℤ) < (K : ℤ)
    exact ⟨by positivity, by exact_mod_cast (p.2 j).isLt⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert (hs' j).1 using 1; ring
  · convert (hs' j).2 using 1; ring
  · exact rough_residue_endpoint_scaled_bound _ _ _ hk hu C Z (hpos j).1 hscale
  · exact rough_residue_endpoint_scaled_bound _ _ _ hk hu C Z (hpos j).2 hscale

end Hindman168
