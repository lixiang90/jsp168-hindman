import Hindman168.PadicPolynomialCongruence
import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Exact uniform finite p-power residue fibers of probability Haar

Every residue fiber is a closed norm ball. Translation invariance makes
their measures equal, and the finite partition of the whole probability
space fixes the common measure to 1/p^e. No distributional assumption is
introduced for the finite residue map.
-/

namespace Hindman168

open MeasureTheory Filter
open scoped BigOperators Topology Classical

variable (p : ℕ) [Fact p.Prime]

theorem padicResidueFiber_eq_norm (e : ℕ) (a : ZMod (p ^ e)) :
    {x : ℤ_[p] | PadicInt.toZModPow e x = a} =
      {x | ‖x - (a.val : ℤ_[p])‖ ≤ ((p : ℝ)⁻¹) ^ e} := by
  have hv : PadicInt.toZModPow e (a.val : ℤ_[p]) = a := by
    rw [map_natCast, ZMod.natCast_zmod_val]
  ext x
  have hk : PadicInt.toZModPow e (x - (a.val : ℤ_[p])) = 0 ↔
      PadicInt.toZModPow e x = a := by rw [map_sub, hv, sub_eq_zero]
  rw [Set.mem_setOf_eq, ← hk, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    ← PadicInt.norm_le_pow_iff_mem_span_pow]
  simp only [Set.mem_setOf_eq, zpow_neg, zpow_natCast, inv_pow]

variable [MeasurableSpace ℤ_[p]] [BorelSpace ℤ_[p]]

theorem padicResidueFiber_measurable (e : ℕ) (a : ZMod (p ^ e)) :
    MeasurableSet {x : ℤ_[p] | PadicInt.toZModPow e x = a} := by
  rw [padicResidueFiber_eq_norm]
  exact (isClosed_le (continuous_id.sub continuous_const).norm continuous_const).measurableSet

theorem padicResidueMap_measurable (e : ℕ) : Measurable (PadicInt.toZModPow e : ℤ_[p] → ZMod (p ^ e)) := by
  intro S _
  rw [← Set.biUnion_preimage_singleton (PadicInt.toZModPow e) S]
  exact MeasurableSet.biUnion (Set.to_countable S) (fun a _ => padicResidueFiber_measurable p e a)

theorem padicResidueHaar_fiber_eq_zero (e : ℕ) (a : ZMod (p ^ e)) :
    padicProbabilityHaar p {x | PadicInt.toZModPow e x = a} =
      padicProbabilityHaar p {x | PadicInt.toZModPow e x = 0} := by
  have hv : PadicInt.toZModPow e (a.val : ℤ_[p]) = a := by
    rw [map_natCast, ZMod.natCast_zmod_val]
  have heq : (fun x : ℤ_[p] => (a.val : ℤ_[p]) + x) ⁻¹'
      {x | PadicInt.toZModPow e x = a} = {x | PadicInt.toZModPow e x = 0} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, map_add, hv, add_eq_left]
  have hm := measure_preimage_add (padicProbabilityHaar p) (a.val : ℤ_[p])
    {x | PadicInt.toZModPow e x = a}
  rw [heq] at hm
  exact hm.symm

theorem padicResidueHaar_fiber_uniform (e : ℕ) (a : ZMod (p ^ e)) :
    padicProbabilityHaar p {x | PadicInt.toZModPow e x = a} = (p ^ e : ENNReal)⁻¹ := by
  have hs := sum_measure_preimage_singleton (μ := padicProbabilityHaar p)
    (Finset.univ : Finset (ZMod (p ^ e))) (fun a _ => padicResidueFiber_measurable p e a)
  have hzero : (p ^ e : ENNReal) *
      padicProbabilityHaar p {x | PadicInt.toZModPow e x = 0} = 1 := by
    simp only [Finset.coe_univ, Set.preimage_univ] at hs
    change (∑ a : ZMod (p ^ e), padicProbabilityHaar p {x | PadicInt.toZModPow e x = a}) =
      padicProbabilityHaar p Set.univ at hs
    simp only [measure_univ, padicResidueHaar_fiber_eq_zero, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_pow] at hs
    exact hs
  rw [padicResidueHaar_fiber_eq_zero]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hzero)

theorem padicResidueHaar_map_singleton (e : ℕ) (a : ZMod (p ^ e)) :
    (padicProbabilityHaar p).map (PadicInt.toZModPow e) {a} = (p ^ e : ENNReal)⁻¹ := by
  rw [Measure.map_apply (padicResidueMap_measurable p e) (measurableSet_singleton a)]
  exact padicResidueHaar_fiber_uniform p e a

end Hindman168
