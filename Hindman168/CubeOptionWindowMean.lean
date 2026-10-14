import Hindman168.AlignmentBoxReindex
import Hindman168.CubeStandardAlphaBox

/-! The Option-indexed original cube average equals the standard Fin-indexed
cube average with the SAME point source and exact residue/ceil box. -/
namespace Hindman168
open scoped BigOperators Classical

theorem cube_option_standard_window_mean {X : Type*} (d : ℕ) (beta L α : ℝ) (b t : ℤ)
    (P : ℤ → X) (f : (Finset (Fin d) → X) → ℂ) :
    finiteComplexSetMean (alignmentBoxClass
      (fun z => ⌈cubeAlphaLower d beta L ((finSuccEquiv d).symm z)⌉)
      (fun z => ⌈cubeAlphaUpper d beta L α ((finSuccEquiv d).symm z)⌉)
      (fun z => cubeAlphaResidue d b ((finSuccEquiv d).symm z)) t)
      (fun ell => f (fun V => P (ell none+∑ j ∈ V,ell (some j)))) =
    finiteComplexSetMean (alignmentBoxClass
      (fun z => ⌈cubeAlphaLower d beta L z⌉) (fun z => ⌈cubeAlphaUpper d beta L α z⌉)
      (cubeAlphaResidue d b) t)
      (fun x => f (fun V => P (x 0+∑ j ∈ V,x j.succ))) := by
  have h := alignment_box_reindex_mean (finSuccEquiv d)
    (fun z => ⌈cubeAlphaLower d beta L ((finSuccEquiv d).symm z)⌉)
    (fun z => ⌈cubeAlphaUpper d beta L α ((finSuccEquiv d).symm z)⌉)
    (fun z => cubeAlphaResidue d b ((finSuccEquiv d).symm z)) t
    (fun x => f (fun V => P (x 0+∑ j ∈ V,x j.succ)))
  simpa only [Function.comp_def,Equiv.symm_apply_apply,finSuccEquiv_zero,finSuccEquiv_succ] using h

end Hindman168
