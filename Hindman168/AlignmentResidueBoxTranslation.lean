import Hindman168.ComplexBoxTranslation
import Hindman168.AlignmentRetainedEndpointBounds

namespace Hindman168
open scoped BigOperators Classical

theorem alignmentBoxClass_one {ι : Type*} [Fintype ι] (L U r : ι → ℤ) :
    alignmentBoxClass L U r 1 = Fintype.piFinset (fun j => Finset.Ico (L j) (U j)) := by
  unfold alignmentBoxClass alignmentIntervalClass
  simp [Int.ModEq]

theorem alignment_residue_box_division_mean {ι : Type*} [Fintype ι]
    (L U r : ι → ℤ) (d : ℤ) (hd : 0 < d) (f : (ι → ℤ) → ℂ) :
    finiteComplexSetMean (alignmentBoxClass L U r d) f =
      finiteComplexSetMean (Fintype.piFinset (fun j =>
        Finset.Ico (alignmentRetainedEndpoint (L j) d (r j))
          (alignmentRetainedEndpoint (U j) d (r j))))
        (fun z => f (fun j => r j + d * z j)) := by
  simpa only [mul_one, mul_zero, add_zero, alignmentBoxClass_one] using
    alignment_retained_box_mean L U r (fun _ => 0) d 1 hd f

theorem alignment_residue_box_translation_bound {ι : Type*} [Fintype ι]
    (L U r v : ι → ℤ) (d : ℤ) (hd : 0 < d) (hlen : ∀ j, 2 * d ≤ U j - L j)
    (f : (ι → ℤ) → ℂ) (K : ℝ) (hK : 0 ≤ K) (hf : ∀ z, ‖f z‖ ≤ K) :
    ‖finiteComplexSetMean (alignmentBoxClass L U r d) (fun z => f (fun j => z j + d * v j)) -
      finiteComplexSetMean (alignmentBoxClass L U r d) f‖ ≤
      K * ∑ j, 4 * |((d * v j : ℤ) : ℝ)| / ((U j : ℝ) - L j) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have herr (j : ι) := alignmentRetainedEndpoint_side_error (L j) (U j) d (r j) hd
  have hpos (j : ι) : alignmentRetainedEndpoint (L j) d (r j) <
      alignmentRetainedEndpoint (U j) d (r j) := by
    have he := (abs_lt.mp (herr j)).1
    have hh := hlen j
    nlinarith
  rw [alignment_residue_box_division_mean L U r d hd,
    alignment_residue_box_division_mean L U r d hd]
  have h := complex_box_translation_bound
    (fun j => alignmentRetainedEndpoint (L j) d (r j))
    (fun j => alignmentRetainedEndpoint (U j) d (r j)) v hpos
    (fun z => f (fun j => r j + d * z j)) K hK (fun z => hf _)
  have he : (fun z : ι → ℤ => f (fun j => r j + d * (z j + v j))) =
      (fun z => f (fun j => (r j + d * z j) + d * v j)) := by
    funext z
    congr 1
    funext j
    ring
  rw [he] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hK
  apply Finset.sum_le_sum
  intro j _
  have hm : (0 : ℝ) < (alignmentRetainedEndpoint (U j) d (r j) : ℝ) -
      alignmentRetainedEndpoint (L j) d (r j) := by exact_mod_cast sub_pos.mpr (hpos j)
  have hl : 2 * (d : ℝ) ≤ (U j : ℝ) - L j := by exact_mod_cast hlen j
  have hp : (0 : ℝ) < (U j : ℝ) - L j := by linarith
  have hs : |(d : ℝ) * ((alignmentRetainedEndpoint (U j) d (r j) : ℝ) -
      alignmentRetainedEndpoint (L j) d (r j)) - ((U j : ℝ) - L j)| < d := by
    exact_mod_cast herr j
  have hh : (U j : ℝ) - L j ≤ 2 * (d : ℝ) *
      ((alignmentRetainedEndpoint (U j) d (r j) : ℝ) - alignmentRetainedEndpoint (L j) d (r j)) := by
    nlinarith [(abs_lt.mp hs).1]
  rw [Int.cast_mul, abs_mul, abs_of_pos hdR]
  apply (div_le_div_iff₀ hm hp).mpr
  have ht := mul_le_mul_of_nonneg_left hh (abs_nonneg (v j : ℝ))
  nlinarith [ht]

theorem alignment_residue_box_divisible_translation_bound {ι : Type*} [Fintype ι]
    (L U r u : ι → ℤ) (d : ℤ) (hd : 0 < d) (hu : ∀ j, d ∣ u j)
    (hlen : ∀ j, 2 * d ≤ U j - L j)
    (f : (ι → ℤ) → ℂ) (K : ℝ) (hK : 0 ≤ K) (hf : ∀ z, ‖f z‖ ≤ K) :
    ‖finiteComplexSetMean (alignmentBoxClass L U r d) (fun z => f (fun j => z j + u j)) -
      finiteComplexSetMean (alignmentBoxClass L U r d) f‖ ≤
      K * ∑ j, 4 * |(u j : ℝ)| / ((U j : ℝ) - L j) := by
  choose v hv using hu
  have h := alignment_residue_box_translation_bound L U r v d hd hlen f K hK hf
  simpa only [← hv] using h

theorem alignment_residue_box_translation_scale_bound {ι : Type*} [Fintype ι]
    (L U r u : ι → ℤ) (d : ℤ) (hd : 0 < d) (hu : ∀ j, d ∣ u j)
    (Z c : ℝ) (hcZ : 0 < c * Z) (hdZ : 2 * (d : ℝ) ≤ c * Z)
    (hlen : ∀ j, c * Z ≤ (U j : ℝ) - L j)
    (f : (ι → ℤ) → ℂ) (K : ℝ) (hK : 0 ≤ K) (hf : ∀ z, ‖f z‖ ≤ K) :
    ‖finiteComplexSetMean (alignmentBoxClass L U r d) (fun z => f (fun j => z j + u j)) -
      finiteComplexSetMean (alignmentBoxClass L U r d) f‖ ≤
      4 * K * (∑ j, |(u j : ℝ)|) / (c * Z) := by
  have h2 (j : ι) : 2 * d ≤ U j - L j := by exact_mod_cast hdZ.trans (hlen j)
  apply (alignment_residue_box_divisible_translation_bound L U r u d hd hu h2 f K hK hf).trans
  calc
    _ ≤ K * ∑ j, 4 * |(u j : ℝ)| / (c * Z) := by
      apply mul_le_mul_of_nonneg_left _ hK
      exact Finset.sum_le_sum (fun j _ => div_le_div_of_nonneg_left (by positivity) hcZ (hlen j))
    _ = _ := by rw [← Finset.sum_div, ← Finset.mul_sum]; ring

end Hindman168
