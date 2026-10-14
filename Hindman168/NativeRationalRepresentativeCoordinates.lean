import Hindman168.NativeRationalFirstLayerCoordinates
import Hindman168.NativeRationalSelectedRepresentatives
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.Floor.Ring

/-! Selected compact representatives are not assumed fractional sections.
Their true first-layer coordinates differ from fractional parts by bounded
integer vectors, in ONE finite geometry-only box. -/
namespace Hindman168
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_first_layer_representative_bound {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a ∈ nativeRationalRepresentativeSet D,
      ∀ i, |nativeRationalFirstLayerCoordinates D L a i| ≤ B := by
  obtain ⟨b,hb⟩ := (native_rational_representative_set_compact D).bddAbove_image
    ((native_rational_first_layer_coordinates_continuous D L).norm.continuousOn)
  refine ⟨max b 0,le_max_right _ _,?_⟩
  intro a ha i
  exact (show |nativeRationalFirstLayerCoordinates D L a i| ≤ ‖nativeRationalFirstLayerCoordinates D L a‖ by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (nativeRationalFirstLayerCoordinates D L a) i).trans
    ((hb (Set.mem_image_of_mem _ ha)).trans (le_max_left _ _))

noncomputable def nativeRationalRepresentativeCoordinateOffset {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (g : D.G) :
    NativeRationalFirstLayerIndex D L → ℤ :=
  fun i => ⌊nativeRationalFirstLayerCoordinates D L (nativeRationalRepresentative D g) i⌋

theorem native_rational_representative_fractional_coordinates {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (g : D.G) (i : NativeRationalFirstLayerIndex D L) :
    nativeRationalFirstLayerCoordinates D L (nativeRationalRepresentative D g) i =
      Int.fract (nativeRationalFirstLayerCoordinates D L g i)+
        (nativeRationalRepresentativeCoordinateOffset D L g i : ℝ) := by
  obtain ⟨k,hk⟩ := native_rational_first_layer_coordinate_integral D L i
    (nativeRationalRepresentativeLatticePart D g) (nativeRationalRepresentativeLatticePart D g).property
  have he := congrFun (native_rational_first_layer_coordinates_mul D L
    (nativeRationalRepresentative D g) (nativeRationalRepresentativeLatticePart D g)) i
  rw [← native_rational_representative_factorization D g] at he
  change nativeRationalFirstLayerCoordinates D L g i =
    nativeRationalFirstLayerCoordinates D L (nativeRationalRepresentative D g) i+_ at he
  change nativeRationalFirstLayerCoordinates D L (nativeRationalRepresentativeLatticePart D g) i=(k : ℝ) at hk
  rw [hk] at he
  rw [he,Int.fract_add_intCast]
  change _ = Int.fract _+(⌊nativeRationalFirstLayerCoordinates D L (nativeRationalRepresentative D g) i⌋ : ℝ)
  rw [Int.fract]
  ring

theorem native_rational_representative_offsets_finite {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    ∃ K : ℕ, ∃ C : Finset (NativeRationalFirstLayerIndex D L → ℤ), C.Nonempty ∧
      (∀ b ∈ C, ∀ i, |(b i : ℝ)| ≤ (K : ℝ)) ∧
      ∀ g, nativeRationalRepresentativeCoordinateOffset D L g ∈ C := by
  obtain ⟨B,hB,hbound⟩ := native_rational_first_layer_representative_bound D L
  obtain ⟨K,hK⟩ := exists_nat_gt (B+1)
  let C := Fintype.piFinset (fun _ : NativeRationalFirstLayerIndex D L => Finset.Icc (-(K : ℤ)) (K : ℤ))
  refine ⟨K,C,?_,?_,?_⟩
  · apply Fintype.piFinset_nonempty.mpr
    intro i
    exact ⟨0,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩
  · intro b hb i
    have hi := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hb i)
    apply abs_le.mpr
    constructor
    · exact_mod_cast hi.1
    · exact_mod_cast hi.2
  · intro g
    apply Fintype.mem_piFinset.mpr
    intro i
    have he := native_rational_representative_fractional_coordinates D L g i
    have hb := abs_le.mp (hbound _ (native_rational_representative_mem D g) i)
    have h0 := Int.fract_nonneg (nativeRationalFirstLayerCoordinates D L g i)
    have h1 := Int.fract_lt_one (nativeRationalFirstLayerCoordinates D L g i)
    have hl : -(K : ℝ) ≤ (nativeRationalRepresentativeCoordinateOffset D L g i : ℝ) := by linarith
    have hu : (nativeRationalRepresentativeCoordinateOffset D L g i : ℝ) ≤ (K : ℝ) := by linarith
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hl,by exact_mod_cast hu⟩

end Hindman168
