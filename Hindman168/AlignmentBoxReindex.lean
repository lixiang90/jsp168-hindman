import Hindman168.AlignmentBoxMeans
import Mathlib.Logic.Equiv.Fin.Basic

/-! Bijective coordinate reindexing preserves the exact residue box and its
normalized finite mean, including empty boxes. -/
namespace Hindman168
open scoped Classical

theorem alignment_box_reindex_image {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A B r : κ → ℤ) (d : ℤ) :
    (alignmentBoxClass A B r d).image (fun x j => x (e j)) =
      alignmentBoxClass (A ∘ e) (B ∘ e) (r ∘ e) d := by
  ext x
  constructor
  · intro hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    exact Fintype.mem_piFinset.mpr (fun j => Fintype.mem_piFinset.mp hz (e j))
  · intro hx
    refine Finset.mem_image.mpr ⟨fun k => x (e.symm k),?_,?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro k
      simpa only [Function.comp_apply,e.apply_symm_apply] using Fintype.mem_piFinset.mp hx (e.symm k)
    · funext j
      simp only [e.symm_apply_apply]

theorem alignment_box_reindex_mean {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A B r : κ → ℤ) (d : ℤ) (f : (ι → ℤ) → ℂ) :
    finiteComplexSetMean (alignmentBoxClass A B r d) (fun x => f (fun j => x (e j))) =
      finiteComplexSetMean (alignmentBoxClass (A ∘ e) (B ∘ e) (r ∘ e) d) f := by
  rw [← alignment_box_reindex_image]
  symm
  apply finiteComplexSetMean_image
  intro x y h
  funext k
  simpa only [e.apply_symm_apply] using congrFun h (e.symm k)

end Hindman168
