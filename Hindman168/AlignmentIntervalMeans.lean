import Hindman168.FiniteComplexSetMean
import Hindman168.AlignmentResidueEndpoints

namespace Hindman168
open scoped Classical

noncomputable def alignmentIntervalClass (A B d r : ℤ) : Finset ℤ :=
  (Finset.Ico A B).filter (fun z => Int.ModEq d r z)

theorem alignment_affine_class_image (t d b A B r : ℤ) (ht : 0 < t) :
    (alignmentIntervalClass A B d r).image (fun ell => b + t * ell) =
      alignmentIntervalClass (b + t * A) (b + t * B) (t * d) (b + t * r) := by
  ext z
  simpa only [alignmentIntervalClass, Finset.mem_filter, Finset.mem_Ico, and_assoc] using
    alignment_affine_interval_residue_image t d b A B r z ht

theorem alignment_affine_class_mean (t d b A B r : ℤ) (ht : 0 < t) (f : ℤ → ℂ) :
    finiteComplexSetMean (alignmentIntervalClass A B d r) (fun ell => f (b + t * ell)) =
      finiteComplexSetMean
        (alignmentIntervalClass (b + t * A) (b + t * B) (t * d) (b + t * r)) f := by
  rw [← alignment_affine_class_image t d b A B r ht]
  have hg : Function.Injective (fun ell : ℤ => b + t * ell) := by
    intro a a' h
    nlinarith
  exact (finiteComplexSetMean_image _ (fun ell : ℤ => b + t * ell) hg f).symm

theorem alignment_cube_class_mean (M t p Y A B r d : ℤ) (ht : 0 < t) (f : ℤ → ℂ) :
    finiteComplexSetMean (alignmentIntervalClass A B d r) (fun ell => f (alignmentCubeBase M t p Y ell)) =
      finiteComplexSetMean (alignmentIntervalClass
        (alignmentCubeBase M t p Y A) (alignmentCubeBase M t p Y B)
        (t * d) (alignmentCubeBase M t p Y r)) f := by
  have he (ell : ℤ) : alignmentCubeBase M t p Y ell = (t * p / M - Y) + t * ell := by
    unfold alignmentCubeBase
    ring
  simp only [he]
  exact alignment_affine_class_mean t d (t * p / M - Y) A B r ht f

theorem alignment_endpoint_class_mean (A B d r : ℤ) (hd : 0 < d) (f : ℤ → ℂ) :
    finiteComplexSetMean (alignmentIntervalClass A B d r) f =
      finiteComplexSetMean (alignmentIntervalClass
        (alignmentResidueEndpoint A d r) (alignmentResidueEndpoint B d r) d r) f := by
  unfold alignmentIntervalClass
  rw [alignmentResidueEndpoint_interval_exact A B d r hd]

end Hindman168
