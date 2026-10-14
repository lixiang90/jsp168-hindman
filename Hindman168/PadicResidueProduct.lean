import Hindman168.PadicPolynomialFamily

/-!
# Exact finite residue-vector probabilities of independent p-adic Haar

Vector fibers are products of the proved scalar fibers. Finite bad-event
counts divided by the complete grid size therefore equal the original
Haar probabilities, including polynomial congruence events.
-/

namespace Hindman168

open MeasureTheory Filter
open scoped BigOperators Topology Classical

variable (p : ℕ) [Fact p.Prime]

noncomputable def padicResidueVector (e n : ℕ) (x : Fin n → ℤ_[p]) : Fin n → ZMod (p ^ e) :=
  fun i => PadicInt.toZModPow e (x i)

variable [MeasurableSpace ℤ_[p]] [BorelSpace ℤ_[p]]

theorem padicResidueVector_measurable (e n : ℕ) : Measurable (padicResidueVector p e n) :=
  measurable_pi_iff.mpr (fun i => (padicResidueMap_measurable p e).comp (measurable_pi_apply i))

theorem padicResidueVector_fiber (e n : ℕ) (a : Fin n → ZMod (p ^ e)) :
    (Measure.pi (fun _ : Fin n => padicProbabilityHaar p))
      ((padicResidueVector p e n) ⁻¹' {a}) = ((p ^ e : ENNReal) ^ n)⁻¹ := by
  have heq : (padicResidueVector p e n) ⁻¹' {a} =
      Set.univ.pi (fun i => {x : ℤ_[p] | PadicInt.toZModPow e x = a i}) := by
    ext x
    simp [padicResidueVector, funext_iff]
  rw [heq, Measure.pi_pi]
  simp only [padicResidueHaar_fiber_uniform, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.inv_pow]

theorem padicResidueVector_finite_event (e n : ℕ) (S : Finset (Fin n → ZMod (p ^ e))) :
    (Measure.pi (fun _ : Fin n => padicProbabilityHaar p))
      ((padicResidueVector p e n) ⁻¹' (S : Set (Fin n → ZMod (p ^ e)))) =
      (S.card : ENNReal) / (p ^ e : ENNReal) ^ n := by
  have h := sum_measure_preimage_singleton
    (μ := Measure.pi (fun _ : Fin n => padicProbabilityHaar p)) S
    (fun a _ => (padicResidueVector_measurable p e n) (measurableSet_singleton a))
  rw [← h]
  simp only [padicResidueVector_fiber, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

omit [MeasurableSpace ℤ_[p]] [BorelSpace ℤ_[p]] in
theorem padicIntegerPolynomial_reduce_eval {n : ℕ} (e : ℕ)
    (f : MvPolynomial (Fin n) ℤ) (x : Fin n → ℤ_[p]) :
    PadicInt.toZModPow e (MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℤ_[p]) f)) =
      MvPolynomial.eval (padicResidueVector p e n x)
        (MvPolynomial.map (Int.castRingHom (ZMod (p ^ e))) f) := by
  have hc : (PadicInt.toZModPow e).comp (Int.castRingHom ℤ_[p]) =
      Int.castRingHom (ZMod (p ^ e)) := by ext z; simp
  simp only [← MvPolynomial.eval₂_eq_eval_map, MvPolynomial.eval₂_comp_left, hc]
  rfl

noncomputable def finitePolynomialZeros {n : ℕ} (q : ℕ) [NeZero q]
    (f : MvPolynomial (Fin n) ℤ) : Finset (Fin n → ZMod q) :=
  Finset.univ.filter (fun x => MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom (ZMod q)) f) = 0)

theorem padicPolynomial_congruence_finite_count {n : ℕ} (e : ℕ) (f : MvPolynomial (Fin n) ℤ) :
    (Measure.pi (fun _ : Fin n => padicProbabilityHaar p))
      (padicCongruenceEvent p (MvPolynomial.map (Int.castRingHom ℤ_[p]) f) e) =
      ((finitePolynomialZeros (p ^ e) f).card : ENNReal) / (p ^ e : ENNReal) ^ n := by
  have heq : padicCongruenceEvent p (MvPolynomial.map (Int.castRingHom ℤ_[p]) f) e =
      (padicResidueVector p e n) ⁻¹' (finitePolynomialZeros (p ^ e) f : Set (Fin n → ZMod (p ^ e))) := by
    ext x
    simp only [padicCongruenceEvent, Set.mem_setOf_eq, Set.mem_preimage,
      Finset.mem_coe, finitePolynomialZeros, Finset.mem_filter, Finset.mem_univ, true_and,
      padicIntegerPolynomial_reduce_eval]
  rw [heq, padicResidueVector_finite_event]

theorem finitePolynomial_zero_ratio_tendsto {n : ℕ} (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) :
    Tendsto (fun e => ((finitePolynomialZeros (p ^ e) f).card : ENNReal) /
      (p ^ e : ENNReal) ^ n) atTop (𝓝 0) := by
  simpa only [padicPolynomial_congruence_finite_count] using
    integerPolynomial_padicCongruenceProbability_tendsto_zero p f hf

end Hindman168
