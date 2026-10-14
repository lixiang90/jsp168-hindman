import Hindman168.AlignmentResidueBoxTranslation

namespace Hindman168
open scoped BigOperators Classical

theorem alignment_single_coordinate_translation_scale_bound {ι : Type*} [Fintype ι]
    (L U r : ι → ℤ) (a : ι) (delta d : ℤ) (hd : 0 < d) (hdelta : d ∣ delta)
    (Z c : ℝ) (hcZ : 0 < c * Z) (hdZ : 2 * (d : ℝ) ≤ c * Z)
    (hlen : ∀ j, c * Z ≤ (U j : ℝ) - L j)
    (f : (ι → ℤ) → ℂ) (K : ℝ) (hK : 0 ≤ K) (hf : ∀ z, ‖f z‖ ≤ K) :
    ‖finiteComplexSetMean (alignmentBoxClass L U r d)
        (fun z => f (fun j => z j + if j = a then delta else 0)) -
      finiteComplexSetMean (alignmentBoxClass L U r d) f‖ ≤ 4 * K * |(delta : ℝ)| / (c * Z) := by
  have hu : ∀ j : ι, d ∣ if j = a then delta else 0 := by
    intro j
    split_ifs
    · exact hdelta
    · exact dvd_zero d
  have h := alignment_residue_box_translation_scale_bound L U r
    (fun j => if j = a then delta else 0) d hd hu Z c hcZ hdZ hlen f K hK hf
  simpa only [Int.cast_ite, Int.cast_zero, apply_ite abs, abs_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

end Hindman168
