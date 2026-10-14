import Hindman168.AlignmentBoxMeans

namespace Hindman168
open scoped Classical

def alignmentRetainedEndpoint (L D a : ℤ) : ℤ := (alignmentResidueEndpoint L D a - a) / D

theorem alignmentRetainedEndpoint_reconstruct (L D a : ℤ) :
    a + D * alignmentRetainedEndpoint L D a = alignmentResidueEndpoint L D a := by
  have hdiv := Int.modEq_iff_dvd.mp (alignmentResidueEndpoint_modEq L D a).symm
  unfold alignmentRetainedEndpoint
  rw [Int.mul_ediv_cancel' hdiv]
  ring

theorem alignment_coarse_endpoint_class (L U D t a b : ℤ) (hD : 0 < D) :
    alignmentIntervalClass L U (D * t) (a + D * b) =
      alignmentIntervalClass (alignmentResidueEndpoint L D a) (alignmentResidueEndpoint U D a)
        (D * t) (a + D * b) := by
  ext z
  simp only [alignmentIntervalClass, Finset.mem_filter, Finset.mem_Ico]
  by_cases hz : Int.ModEq (D * t) (a + D * b) z
  · have hc : Int.ModEq D a z :=
      (Int.modEq_iff_add_fac.mpr ⟨b, rfl⟩).trans (hz.of_dvd (dvd_mul_right D t))
    have hl := alignmentResidueEndpoint_le_iff L D a z hD hc
    have hu := alignmentResidueEndpoint_le_iff U D a z hD hc
    simp only [hz, and_true, ← not_le, hl, hu]
  · simp only [hz, and_false]

theorem alignment_retained_class_mean (L U D t a b : ℤ) (hD : 0 < D) (f : ℤ → ℂ) :
    finiteComplexSetMean (alignmentIntervalClass L U (D * t) (a + D * b)) f =
      finiteComplexSetMean (alignmentIntervalClass (alignmentRetainedEndpoint L D a)
        (alignmentRetainedEndpoint U D a) t b) (fun z => f (a + D * z)) := by
  rw [alignment_coarse_endpoint_class L U D t a b hD,
    ← alignmentRetainedEndpoint_reconstruct L D a,
    ← alignmentRetainedEndpoint_reconstruct U D a]
  exact (alignment_affine_class_mean D t a _ _ b hD f).symm

theorem alignment_retained_box_mean {ι : Type*} [Fintype ι]
    (L U a b : ι → ℤ) (D t : ℤ) (hD : 0 < D) (f : (ι → ℤ) → ℂ) :
    finiteComplexSetMean (alignmentBoxClass L U (fun j => a j + D * b j) (D * t)) f =
      finiteComplexSetMean (alignmentBoxClass (fun j => alignmentRetainedEndpoint (L j) D (a j))
        (fun j => alignmentRetainedEndpoint (U j) D (a j)) b t)
        (fun z => f (fun j => a j + D * z j)) := by
  have he : alignmentBoxClass L U (fun j => a j + D * b j) (D * t) =
      alignmentBoxClass (fun j => a j + D * alignmentRetainedEndpoint (L j) D (a j))
        (fun j => a j + D * alignmentRetainedEndpoint (U j) D (a j))
        (fun j => a j + D * b j) (D * t) := by
    unfold alignmentBoxClass
    congr 1
    funext j
    simp only [alignmentRetainedEndpoint_reconstruct]
    exact alignment_coarse_endpoint_class (L j) (U j) D t (a j) (b j) hD
  rw [he]
  exact (alignment_affine_box_mean _ _ b a D t hD f).symm

end Hindman168
