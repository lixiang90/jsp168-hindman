import Hindman168.AlignmentClassCounts
import Mathlib.Data.Fintype.BigOperators

namespace Hindman168
open scoped BigOperators Classical

noncomputable def alignmentBoxClass {ι : Type*} [Fintype ι]
    (A B r : ι → ℤ) (d : ℤ) : Finset (ι → ℤ) :=
  Fintype.piFinset (fun j => alignmentIntervalClass (A j) (B j) d (r j))

theorem alignmentBoxClass_card {ι : Type*} [Fintype ι] (A B r : ι → ℤ) (d : ℤ) :
    (alignmentBoxClass A B r d).card = ∏ j, (alignmentIntervalClass (A j) (B j) d (r j)).card := by
  exact Fintype.card_piFinset _

theorem alignmentBoxClass_nonempty {ι : Type*} [Fintype ι]
    (A B r : ι → ℤ) (d : ℕ) (hd : 0 < d) (hlen : ∀ j, 2 * (d : ℤ) ≤ B j - A j) :
    (alignmentBoxClass A B r d).Nonempty := by
  apply Fintype.piFinset_nonempty.mpr
  exact fun j => alignment_interval_class_nonempty (A j) (B j) (r j) d hd (hlen j)

theorem alignment_affine_box_image {ι : Type*} [Fintype ι]
    (A B r b : ι → ℤ) (t d : ℤ) (ht : 0 < t) :
    (alignmentBoxClass A B r d).image (fun z j => b j + t * z j) =
      alignmentBoxClass (fun j => b j + t * A j) (fun j => b j + t * B j)
        (fun j => b j + t * r j) (t * d) := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    apply Fintype.mem_piFinset.mpr
    intro j
    rw [← alignment_affine_class_image t d (b j) (A j) (B j) (r j) ht]
    exact Finset.mem_image.mpr ⟨a j, Fintype.mem_piFinset.mp ha j, rfl⟩
  · intro hz
    have hh : ∀ j, ∃ a : ℤ, a ∈ alignmentIntervalClass (A j) (B j) d (r j) ∧
        b j + t * a = z j := by
      intro j
      have hj := Fintype.mem_piFinset.mp hz j
      rw [← alignment_affine_class_image t d (b j) (A j) (B j) (r j) ht] at hj
      exact Finset.mem_image.mp hj
    choose a ha he using hh
    exact Finset.mem_image.mpr ⟨a, Fintype.mem_piFinset.mpr ha, funext he⟩

theorem alignment_affine_box_mean {ι : Type*} [Fintype ι]
    (A B r b : ι → ℤ) (t d : ℤ) (ht : 0 < t) (f : (ι → ℤ) → ℂ) :
    finiteComplexSetMean (alignmentBoxClass A B r d) (fun z => f (fun j => b j + t * z j)) =
      finiteComplexSetMean (alignmentBoxClass (fun j => b j + t * A j)
        (fun j => b j + t * B j) (fun j => b j + t * r j) (t * d)) f := by
  have hg : Function.Injective (fun z : ι → ℤ => fun j => b j + t * z j) := by
    intro z z' h
    funext j
    have hj := congrFun h j
    dsimp only at hj
    nlinarith
  rw [← alignment_affine_box_image A B r b t d ht]
  exact (finiteComplexSetMean_image _ _ hg f).symm

end Hindman168
