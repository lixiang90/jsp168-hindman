import Hindman168.RoughNestedResidueSampling
import Hindman168.RoughRealBoxCeil

/-! Exact real-to-integer residual box endpoints and genuine nonempty
coarse/fine samples. Original real endpoints and compatible residues vary.
No coprimality between retained q and removed t is required. -/
namespace Hindman168
open scoped Classical

theorem rough_residue_real_ceil_endpoint (x : ℝ) (q a : ℤ) (hq : 0 < q) :
    roughResidueCoordinateEndpoint ⌈x⌉ q a = ⌈(x-(a : ℝ))/(q : ℝ)⌉ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  apply eq_of_forall_ge_iff
  intro y
  rw [Int.ceil_le]
  have hmod : Int.ModEq q a (a+q*y) := Int.modEq_iff_add_fac.mpr ⟨y,rfl⟩
  have hend := alignmentResidueEndpoint_le_iff ⌈x⌉ q a (a+q*y) hq hmod
  rw [← rough_residue_coordinate_endpoint_reconstruct ⌈x⌉ q a] at hend
  have hceil : ⌈x⌉ ≤ a+q*y ↔ x ≤ (a : ℝ)+(q : ℝ)*(y : ℝ) := by
    rw [Int.ceil_le]
    push_cast
    rfl
  constructor
  · intro hy
    have hxy : a+q*roughResidueCoordinateEndpoint ⌈x⌉ q a ≤ a+q*y := by
      simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hy hq.le) a
    have hx := hceil.mp (hend.mp hxy)
    apply (div_le_iff₀ hqR).mpr
    nlinarith
  · intro hy
    have hx : x ≤ (a : ℝ)+(q : ℝ)*(y : ℝ) := by
      have hh := (div_le_iff₀ hqR).mp hy
      nlinarith
    have hxy := hend.mpr (hceil.mpr hx)
    have hmul : q*roughResidueCoordinateEndpoint ⌈x⌉ q a ≤ q*y := by omega
    exact le_of_mul_le_mul_left hmul hq

theorem rough_residual_real_box_integer_geometry {κ : Type*}
    (lo hi : κ → ℝ) (a : κ → ℤ) (q : ℕ) (hq : 0 < q)
    (Z c C : ℝ) (hZ : 1 ≤ Z) (_hC : 0 ≤ C) (hlarge : 2 ≤ c*Z)
    (hgeom : ∀ j,
      c*Z ≤ (hi j-(a j : ℝ))/(q : ℝ)-(lo j-(a j : ℝ))/(q : ℝ) ∧
      (hi j-(a j : ℝ))/(q : ℝ)-(lo j-(a j : ℝ))/(q : ℝ) ≤ C*Z ∧
      |(lo j-(a j : ℝ))/(q : ℝ)| ≤ C*Z ∧ |(hi j-(a j : ℝ))/(q : ℝ)| ≤ C*Z) :
    ∀ j, (c/2)*Z ≤ (roughResidueBoxEndpoint (fun j => ⌈hi j⌉) a q j : ℝ)-
        roughResidueBoxEndpoint (fun j => ⌈lo j⌉) a q j ∧
      (roughResidueBoxEndpoint (fun j => ⌈hi j⌉) a q j : ℝ)-
        roughResidueBoxEndpoint (fun j => ⌈lo j⌉) a q j ≤ (2*(C+1))*Z ∧
      |(roughResidueBoxEndpoint (fun j => ⌈lo j⌉) a q j : ℝ)| ≤ (2*(C+1))*Z ∧
      |(roughResidueBoxEndpoint (fun j => ⌈hi j⌉) a q j : ℝ)| ≤ (2*(C+1))*Z := by
  intro j
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  simp only [roughResidueBoxEndpoint,rough_residue_real_ceil_endpoint _ _ _ hqZ,Int.cast_natCast]
  have hlo := alignment_ceil_endpoint_bound ((lo j-(a j : ℝ))/(q : ℝ)) Z C hZ (hgeom j).2.2.1
  have hhi := alignment_ceil_endpoint_bound ((hi j-(a j : ℝ))/(q : ℝ)) Z C hZ (hgeom j).2.2.2
  have hs := alignment_ceil_side_bounds ((lo j-(a j : ℝ))/(q : ℝ))
    ((hi j-(a j : ℝ))/(q : ℝ)) Z c C hZ hlarge (hgeom j).1
    (by simpa only [neg_mul] using (abs_le.mp (hgeom j).2.2.1).1)
    (abs_le.mp (hgeom j).2.2.2).2
  refine ⟨hs.1,?_,?_,?_⟩
  · nlinarith [hs.2]
  · nlinarith
  · nlinarith

theorem rough_residual_real_box_samples_nonempty {κ : Type*} [Fintype κ]
    (lo hi : κ → ℝ) (a b : κ → ℤ) (q t : ℕ) (hq : 0 < q) (ht : 0 < t)
    (Z c C : ℝ) (hZ : 1 ≤ Z) (hC : 0 ≤ C) (hlarge : 2 ≤ c*Z)
    (hstep : 4*(t : ℝ) ≤ c*Z)
    (hgeom : ∀ j,
      c*Z ≤ (hi j-(a j : ℝ))/(q : ℝ)-(lo j-(a j : ℝ))/(q : ℝ) ∧
      (hi j-(a j : ℝ))/(q : ℝ)-(lo j-(a j : ℝ))/(q : ℝ) ≤ C*Z ∧
      |(lo j-(a j : ℝ))/(q : ℝ)| ≤ C*Z ∧ |(hi j-(a j : ℝ))/(q : ℝ)| ≤ C*Z)
    (hcompatible : ∀ j, Int.ModEq q (a j) (b j)) :
    0 < (alignmentBoxClass (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) a q).card ∧
      0 < (alignmentBoxClass (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) b (q*t : ℕ)).card := by
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  obtain ⟨v,hrep,_⟩ := rough_nested_residue_compatible_representatives a b q t hqZ.ne' hcompatible
  have hgeo := rough_residual_real_box_integer_geometry lo hi a q hq Z c C hZ hC hlarge hgeom
  have hlen (j : κ) : 2*(t : ℤ) ≤
      roughResidueBoxEndpoint (fun j => ⌈hi j⌉) a q j-
        roughResidueBoxEndpoint (fun j => ⌈lo j⌉) a q j := by
    have hh : 2*(t : ℝ) ≤ (roughResidueBoxEndpoint (fun j => ⌈hi j⌉) a q j : ℝ)-
        roughResidueBoxEndpoint (fun j => ⌈lo j⌉) a q j := by nlinarith [(hgeo j).1]
    exact_mod_cast hh
  have hfine := alignmentBoxClass_nonempty (roughResidueBoxEndpoint (fun j => ⌈lo j⌉) a q)
    (roughResidueBoxEndpoint (fun j => ⌈hi j⌉) a q) v t ht hlen
  have himage := rough_nested_residue_box_image (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) a v q t hqZ
  have hrep' : b=(fun j => a j+(q : ℤ)*v j) := funext hrep
  have hfineOriginal : (alignmentBoxClass (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) b (q*t : ℕ)).Nonempty := by
    rw [hrep',Nat.cast_mul,← himage]
    exact hfine.image _
  obtain ⟨x,hx⟩ := hfineOriginal
  have hcoarseOriginal : (alignmentBoxClass (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) a q).Nonempty := by
    refine ⟨x,Fintype.mem_piFinset.mpr ?_⟩
    intro j
    obtain ⟨hxI,hxM⟩ := Finset.mem_filter.mp (Fintype.mem_piFinset.mp hx j)
    have hxQ := hxM.of_dvd (show (q : ℤ) ∣ (q*t : ℕ) from by exact_mod_cast dvd_mul_right q t)
    exact Finset.mem_filter.mpr ⟨hxI,(hcompatible j).trans hxQ⟩
  exact ⟨Finset.card_pos.mpr hcoarseOriginal,Finset.card_pos.mpr ⟨x,hx⟩⟩

end Hindman168
