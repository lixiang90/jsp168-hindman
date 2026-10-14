import Hindman168.AlignmentBoxMeans
import Hindman168.ComplexMassTranslation

/-! A genuine finite coordinate equivalence preserves the FULL original
box/residue sample set and normalized law, including empty sets. No dense
subsample, coprimality or normalizing-mass assumption is introduced. -/
namespace Hindman168
open FiniteMass
open scoped Classical

def roughCoordinateReindex {κ τ X : Type*} (e : κ ≃ τ) : (κ → X) ≃ (τ → X) where
  toFun x j := x (e.symm j)
  invFun y j := y (e j)
  left_inv x := by funext j; simp
  right_inv y := by funext j; simp

theorem rough_coordinate_reindex_apply {κ τ X : Type*} (e : κ ≃ τ) (x : κ → X) (j : τ) :
    roughCoordinateReindex e x j=x (e.symm j) := rfl

theorem rough_coordinate_box_image {κ τ : Type*} [Fintype κ] [Fintype τ]
    (e : κ ≃ τ) (lo hi a : κ → ℤ) (q : ℤ) :
    @Finset.image _ _ (Classical.decEq _) (roughCoordinateReindex e) (alignmentBoxClass lo hi a q) =
      alignmentBoxClass (fun j => lo (e.symm j)) (fun j => hi (e.symm j)) (fun j => a (e.symm j)) q := by
  letI : DecidableEq (τ → ℤ) := Classical.decEq _
  ext y
  constructor
  · intro hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact Fintype.mem_piFinset.mpr (fun j => Fintype.mem_piFinset.mp hx (e.symm j))
  · intro hy
    apply Finset.mem_image.mpr
    refine ⟨(roughCoordinateReindex e).symm y,?_,(roughCoordinateReindex e).apply_symm_apply y⟩
    apply Fintype.mem_piFinset.mpr
    intro j
    have h := Fintype.mem_piFinset.mp hy (e j)
    change y (e j) ∈ alignmentIntervalClass (lo j) (hi j) q (a j)
    simpa only [Equiv.symm_apply_apply] using h

theorem rough_coordinate_box_card {κ τ : Type*} [Fintype κ] [Fintype τ]
    (e : κ ≃ τ) (lo hi a : κ → ℤ) (q : ℤ) :
    (alignmentBoxClass (fun j => lo (e.symm j)) (fun j => hi (e.symm j)) (fun j => a (e.symm j)) q).card =
      (alignmentBoxClass lo hi a q).card := by
  letI : DecidableEq (τ → ℤ) := Classical.decEq _
  rw [←rough_coordinate_box_image e lo hi a q]
  exact Finset.card_image_of_injective _ (roughCoordinateReindex e).injective

theorem rough_coordinate_box_uniform_push {κ τ : Type*} [Fintype κ] [Fintype τ]
    (e : κ ≃ τ) (lo hi a : κ → ℤ) (q : ℤ) :
    (uniformFinsetMass (alignmentBoxClass lo hi a q)).mapDomain (roughCoordinateReindex e) =
      uniformFinsetMass (alignmentBoxClass (fun j => lo (e.symm j))
        (fun j => hi (e.symm j)) (fun j => a (e.symm j)) q) := by
  rw [uniformFinsetMass_push _ _ (roughCoordinateReindex e).injective]
  exact congrArg uniformFinsetMass (rough_coordinate_box_image e lo hi a q)

theorem rough_coordinate_box_complex_mean {κ τ : Type*} [Fintype κ] [Fintype τ]
    (e : κ ≃ τ) (lo hi a : κ → ℤ) (q : ℤ) (F : (τ → ℤ) → ℂ) :
    complexExpectation (uniformFinsetMass (alignmentBoxClass (fun j => lo (e.symm j))
      (fun j => hi (e.symm j)) (fun j => a (e.symm j)) q)) F =
      complexExpectation (uniformFinsetMass (alignmentBoxClass lo hi a q))
        (fun x => F (roughCoordinateReindex e x)) := by
  rw [←rough_coordinate_box_uniform_push,complexExpectation_push]

end Hindman168
