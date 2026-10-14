import Hindman168.FiniteTranslateSumError
import Hindman168.IntegerIntervalCubeTranslateBoundary
import Hindman168.IntegerPeriodicCubeAverage
import Hindman168.IntegerCubeResidueShiftBounds
import Hindman168.HaarMeanTestError

namespace Hindman168
open scoped BigOperators Classical

/-- The full signed-increment interval cube mean of the periodic input. -/
noncomputable def integerIntervalPeriodicCubeMean (q d L : ℕ) (f : ZMod q → ℝ) : ℝ :=
  (∑ p ∈ integerIntervalCubeDomain d L, integerPeriodicCubeProduct q d f p) /
    (integerIntervalCubeDomain d L).card

theorem integerIntervalPeriodicCubeMean_translate_error (q d L D : ℕ)
    (hL : 0 < L) (f : ZMod q → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (r : ℤ × (Fin d → ℤ))
    (hr : ∀ ω : Finset (Fin d), 0 ≤ integerCubeVertex r ω ∧ integerCubeVertex r ω ≤ D) :
    |(∑ p ∈ integerIntervalCubeDomain d L, integerPeriodicCubeProduct q d f (p + r)) /
        (integerIntervalCubeDomain d L).card - integerIntervalPeriodicCubeMean q d L f| ≤
      (2 * (2 : ℝ) ^ d * D * (L : ℝ) ^ d) / (integerIntervalCubeDomain d L).card := by
  have hc : (0 : ℝ) < (integerIntervalCubeDomain d L).card := by
    exact_mod_cast (integerIntervalCubeDomain_nonempty d L hL).card_pos
  have hb := finite_translate_sum_difference_bound (integerIntervalCubeDomain d L) r
    (integerPeriodicCubeProduct q d f) (integerPeriodicCubeProduct_abs_le_one q d f hf)
  have hfront : (((integerIntervalCubeDomain d L).filter (fun p =>
      p + r ∉ integerIntervalCubeDomain d L)).card : ℝ) ≤ (2 : ℝ) ^ d * D * (L : ℝ) ^ d := by
    exact_mod_cast integerIntervalCube_translate_out_card_le d L D r hr
  have hback : (((integerIntervalCubeDomain d L).filter (fun p =>
      p - r ∉ integerIntervalCubeDomain d L)).card : ℝ) ≤ (2 : ℝ) ^ d * D * (L : ℝ) ^ d := by
    exact_mod_cast integerIntervalCube_translate_back_out_card_le d L D r hr
  unfold integerIntervalPeriodicCubeMean
  rw [← sub_div, abs_div, abs_of_pos hc]
  have he : (2 : ℝ) ^ d * D * (L : ℝ) ^ d + (2 : ℝ) ^ d * D * (L : ℝ) ^ d =
      2 * (2 : ℝ) ^ d * D * (L : ℝ) ^ d := by ring
  exact div_le_div_of_nonneg_right (hb.trans ((add_le_add hfront hback).trans_eq he)) hc.le

theorem integerIntervalPeriodicCubeMean_residue_average (q d L : ℕ) [NeZero q]
    (hL : 0 < L) (f : ZMod q → ℝ) :
    finiteHaarMean (fun r : ZMod q × (Fin d → ZMod q) =>
      (∑ p ∈ integerIntervalCubeDomain d L,
        integerPeriodicCubeProduct q d f (p + integerCubeResidueShift q d r)) /
          (integerIntervalCubeDomain d L).card) =
      subgroupCubeAverage (⊤ : AddSubgroup (ZMod q)) d f := by
  have hc : ((integerIntervalCubeDomain d L).card : ℝ) ≠ 0 := by
    exact_mod_cast (integerIntervalCubeDomain_nonempty d L hL).card_pos.ne'
  simp only [div_eq_mul_inv]
  rw [finiteHaarMean_mul_const, finiteHaarMean_finset_sum]
  simp_rw [integerPeriodicCubeProduct_mean_residue_shift]
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- The exact residue-translation average and both boundary counts give
the normalized interval-versus-cyclic cube-power discrepancy. -/
theorem integerIntervalPeriodicCubeMean_cyclic_error (q d L : ℕ) [NeZero q]
    (hL : 0 < L) (f : ZMod q → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |integerIntervalPeriodicCubeMean q d L f -
        subgroupCubeAverage (⊤ : AddSubgroup (ZMod q)) d f| ≤
      (2 * (2 : ℝ) ^ d * ((d + 1) * (q - 1) : ℕ) * (L : ℝ) ^ d) /
        (integerIntervalCubeDomain d L).card := by
  let T := fun r : ZMod q × (Fin d → ZMod q) =>
    (∑ p ∈ integerIntervalCubeDomain d L,
      integerPeriodicCubeProduct q d f (p + integerCubeResidueShift q d r)) /
        (integerIntervalCubeDomain d L).card
  have hb := finiteHaarMean_test_error T
    (fun _ => integerIntervalPeriodicCubeMean q d L f)
    ((2 * (2 : ℝ) ^ d * ((d + 1) * (q - 1) : ℕ) * (L : ℝ) ^ d) /
      (integerIntervalCubeDomain d L).card)
    (fun r => integerIntervalPeriodicCubeMean_translate_error q d L
      ((d + 1) * (q - 1)) hL f hf (integerCubeResidueShift q d r)
      (integerCubeResidueShift_vertex_bounds q d r))
  rw [finiteHaarMean_const, integerIntervalPeriodicCubeMean_residue_average q d L hL f] at hb
  rwa [abs_sub_comm]

end Hindman168
