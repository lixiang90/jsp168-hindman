import Hindman168.RoughEqualBoxBoundaryScale
import Hindman168.RoughEqualCubeSampling

namespace Hindman168
open scoped BigOperators Classical

theorem rough_equal_cube_haar_selection {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (width : κ → ℕ) (N : ℕ) (hN : 0 < N)
    (hwidth : ∀ j, N ≤ width j) (f : (κ → ℤ) → ℂ) (mean : ℂ)
    (B η δ : ℝ) (hB : 0 ≤ B) (hf : ∀ x, ‖f x‖ ≤ B)
    (hboundary : 2*B*((roughIntegerWidthBox a width \ roughEqualTiledBox a width N).card : ℝ)/
      (roughIntegerWidthBox a width).card ≤ δ)
    (hbad : η ≤ ‖finiteComplexSetMean (roughIntegerWidthBox a width) f-mean‖) :
    ∃ r : ∀ j, Fin (width j/N),
      η-δ ≤ ‖finiteComplexSetMean (Fintype.piFinset (fun _ : κ => Finset.range N))
        (fun v => f (fun j => roughEqualCubeOrigin a N (fun j => (r j).val) j+(v j : ℤ)))-mean‖ := by
  have hS := rough_integer_width_box_nonempty a width (fun j => hN.trans_le (hwidth j))
  have hT := rough_equal_tiled_box_nonempty a width N hN hwidth
  have hsub := rough_equal_tiled_box_contained a width N
  have hdiscard : (roughIntegerWidthBox a width \ roughEqualTiledBox a width N).card <
      (roughIntegerWidthBox a width).card := by
    rw [Finset.card_sdiff_of_subset hsub]
    have hTpos := hT.card_pos
    have hSpos := hS.card_pos
    omega
  obtain ⟨r, _, hgap⟩ := rough_complex_boundary_haar_selection
    (roughIntegerWidthBox a width) (roughEqualTiledBox a width N) hS hsub
    (by convert hdiscard using 1; congr; exact Subsingleton.elim _ _)
    (roughEqualCubeLabel a width N hN hwidth) f mean B η δ hB hf
    (by convert hboundary using 1; congr; exact Subsingleton.elim _ _) hbad
  refine ⟨r, ?_⟩
  have he := rough_equal_cube_label_fiber a width N hN hwidth r
  have he' : @Finset.filter (κ → ℤ)
      (fun x => roughEqualCubeLabel a width N hN hwidth x = r)
      (fun x => Classical.propDecidable _) (roughEqualTiledBox a width N) =
      roughEqualCube a N (fun j => (r j).val) := by
    convert he using 1; congr
  rw [he', rough_equal_cube_sample_mean] at hgap
  exact hgap

end Hindman168
