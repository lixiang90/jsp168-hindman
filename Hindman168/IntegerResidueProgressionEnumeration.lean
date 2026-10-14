import Hindman168.RoughResidueCoordinateEndpoints
import Hindman168.IntervalResidueCount
import Hindman168.FiniteComplexSetMean

/-! ACTUAL original integer interval residue set is EXACTLY one affine
image of the standard 0<=t<L integer interval, with TRUE length/cardinality
and exact complex mean. No endpoint/tail loss is supplied. -/
namespace Hindman168
open scoped Classical

theorem integer_residue_interval_progression (A B : ℤ) (P : ℕ) (hP : 0 < P)
    (hAB : A ≤ B) (b : Fin P) :
    ∃ (a : ℤ) (L : ℕ),
      intervalResidueSet A (B-A).toNat P b.val=(Finset.Ico 0 (L : ℤ)).image (fun t : ℤ => a+(P : ℤ)*t) ∧
      (intervalResidueSet A (B-A).toNat P b.val).card=L ∧
      ∀ f : ℤ → ℂ, finiteComplexSetMean (intervalResidueSet A (B-A).toNat P b.val) f=
        finiteComplexSetMean (Finset.Ico 0 (L : ℤ)) (fun t => f (a+(P : ℤ)*t)) := by
  have hp : (0 : ℤ) < P := by exact_mod_cast hP
  let U := roughResidueCoordinateEndpoint A (P : ℤ) b.val
  let V := roughResidueCoordinateEndpoint B (P : ℤ) b.val
  have hUV : U ≤ V := rough_residue_coordinate_endpoint_mono (P : ℤ) b.val hp hAB
  let L := (V-U).toNat
  let a := (b.val : ℤ)+(P : ℤ)*U
  have hLen : (L : ℤ)=V-U := Int.toNat_of_nonneg (sub_nonneg.mpr hUV)
  have hShift : (Finset.Ico 0 (L : ℤ)).image (fun t : ℤ => U+t)=Finset.Ico U V := by
    ext t
    simp only [Finset.mem_image,Finset.mem_Ico]
    constructor
    · rintro ⟨u,⟨hu0,huL⟩,rfl⟩
      rw [hLen] at huL
      omega
    · intro ht
      refine ⟨t-U,⟨by omega,?_⟩,by omega⟩
      rw [hLen]
      omega
  have hClass : alignmentIntervalClass A B (P : ℤ) b.val=intervalResidueSet A (B-A).toNat P b.val := by
    have he : A+((B-A).toNat : ℤ)=B := by rw [Int.toNat_of_nonneg (sub_nonneg.mpr hAB)]; omega
    have hbMod : (b.val : ℤ)%(P : ℤ)=(b.val : ℤ) :=
      Int.emod_eq_of_lt (Int.natCast_nonneg b.val) (by exact_mod_cast b.isLt)
    ext t
    simp only [alignmentIntervalClass,intervalResidueSet,integerWindow,Finset.mem_filter,he,Int.ModEq,
      hbMod]
    exact and_congr_right (fun _ => eq_comm)
  have hImage : (Finset.Ico 0 (L : ℤ)).image (fun t : ℤ => a+(P : ℤ)*t)=
      intervalResidueSet A (B-A).toNat P b.val := by
    calc
      _ = ((Finset.Ico 0 (L : ℤ)).image (fun t : ℤ => U+t)).image (fun t : ℤ => (b.val : ℤ)+(P : ℤ)*t) := by
        rw [Finset.image_image]
        apply congrArg (fun f : ℤ → ℤ => (Finset.Ico 0 (L : ℤ)).image f)
        funext t
        dsimp only [Function.comp_apply,a]
        ring
      _ = _ := by rw [hShift,rough_residue_coordinate_interval_image A B (P : ℤ) b.val hp,hClass]
  have hInj : Function.Injective (fun t : ℤ => a+(P : ℤ)*t) := by
    intro x t he
    nlinarith
  refine ⟨a,L,hImage.symm,?_,?_⟩
  · rw [← hImage,Finset.card_image_of_injective _ hInj,Int.card_Ico]
    simp only [sub_zero,Int.toNat_natCast]
  · intro f
    rw [← hImage]
    exact finiteComplexSetMean_image _ _ hInj f

end Hindman168
