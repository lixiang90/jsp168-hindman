import Hindman168.PadicProbabilityHaar
import Mathlib.Tactic.Linarith

/-!
# High p-power congruence probabilities tend to zero

The congruence event is exactly a closed small-norm event. The thresholds
decrease to zero, and continuity from above reduces its probability limit
to the already proved polynomial zero-set measure. This concerns actual
p-adic Haar sampling; identification with finite uniform unit residues
and simultaneous small-prime exponent selection remain separate steps.
-/

namespace Hindman168

open MeasureTheory Filter
open scoped Topology Classical

variable (p : ℕ) [Fact p.Prime]

noncomputable def padicCongruenceEvent {n : ℕ} (f : MvPolynomial (Fin n) ℤ_[p]) (e : ℕ) :
    Set (Fin n → ℤ_[p]) := {x | PadicInt.toZModPow e (MvPolynomial.eval x f) = 0}

theorem padicCongruenceEvent_eq_norm {n : ℕ} (f : MvPolynomial (Fin n) ℤ_[p]) (e : ℕ) :
    padicCongruenceEvent p f e = {x | ‖MvPolynomial.eval x f‖ ≤ ((p : ℝ)⁻¹) ^ e} := by
  ext x
  rw [padicCongruenceEvent, Set.mem_setOf_eq, ← RingHom.mem_ker,
    PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  simp only [Set.mem_setOf_eq, zpow_neg, zpow_natCast, inv_pow]

variable [MeasurableSpace ℤ_[p]] [BorelSpace ℤ_[p]]

theorem padicCongruenceEvent_measurable {n : ℕ} (f : MvPolynomial (Fin n) ℤ_[p]) (e : ℕ) :
    MeasurableSet (padicCongruenceEvent p f e) := by
  rw [padicCongruenceEvent_eq_norm]
  exact (isClosed_le (MvPolynomial.continuous_eval f).norm continuous_const).measurableSet

omit [MeasurableSpace ℤ_[p]] [BorelSpace ℤ_[p]] in
theorem padicCongruenceEvent_antitone {n : ℕ} (f : MvPolynomial (Fin n) ℤ_[p]) :
    Antitone (padicCongruenceEvent p f) := by
  intro a b hab x hx
  rw [padicCongruenceEvent_eq_norm] at hx ⊢
  have hp := Fact.out (p := p.Prime)
  have hpr : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact hx.trans (pow_le_pow_of_le_one (inv_nonneg.mpr (Nat.cast_nonneg p))
    (inv_lt_one_of_one_lt₀ hpr).le hab)

omit [MeasurableSpace ℤ_[p]] [BorelSpace ℤ_[p]] in
theorem padicCongruenceEvent_iInter {n : ℕ} (f : MvPolynomial (Fin n) ℤ_[p]) :
    (⋂ e : ℕ, padicCongruenceEvent p f e) = {x | MvPolynomial.eval x f = 0} := by
  have hp := Fact.out (p := p.Prime)
  have hpr : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have ht : Tendsto (fun e : ℕ => ((p : ℝ)⁻¹) ^ e) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg p))
      (inv_lt_one_of_one_lt₀ hpr)
  ext x
  simp only [Set.mem_iInter, padicCongruenceEvent_eq_norm, Set.mem_setOf_eq]
  constructor
  · intro hx
    have hn : ‖MvPolynomial.eval x f‖ ≤ (0 : ℝ) :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds ht hx
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  · intro hx e
    rw [hx, norm_zero]
    positivity

theorem padicCongruenceProbability_tendsto_zero {n : ℕ} (f : MvPolynomial (Fin n) ℤ_[p])
    (hf : f ≠ 0) :
    Tendsto (fun e => (Measure.pi (fun _ : Fin n => padicProbabilityHaar p))
      (padicCongruenceEvent p f e)) atTop (𝓝 0) := by
  have ht := tendsto_measure_iInter_atTop
    (μ := Measure.pi (fun _ : Fin n => padicProbabilityHaar p))
    (fun e => (padicCongruenceEvent_measurable p f e).nullMeasurableSet)
    (padicCongruenceEvent_antitone p f)
    ⟨0, measure_ne_top _ _⟩
  simpa only [Function.comp_def, padicCongruenceEvent_iInter, padicPolynomial_zero_measure p f hf] using ht

theorem padicCongruenceProbability_eventually_small {n : ℕ} (f : MvPolynomial (Fin n) ℤ_[p])
    (hf : f ≠ 0) {η : ENNReal} (hη : 0 < η) :
    ∃ e0 : ℕ, ∀ e ≥ e0, (Measure.pi (fun _ : Fin n => padicProbabilityHaar p))
      (padicCongruenceEvent p f e) < η := by
  exact eventually_atTop.mp ((padicCongruenceProbability_tendsto_zero p f hf).eventually
    (eventually_lt_nhds hη))

omit [MeasurableSpace ℤ_[p]] [BorelSpace ℤ_[p]] in
theorem integerPolynomial_map_padic_ne_zero {n : ℕ} {f : MvPolynomial (Fin n) ℤ}
    (hf : f ≠ 0) : MvPolynomial.map (Int.castRingHom ℤ_[p]) f ≠ 0 := by
  intro hz
  apply hf
  apply MvPolynomial.map_injective (Int.castRingHom ℤ_[p]) (Int.cast_injective (α := ℤ_[p]))
  simpa only [map_zero] using hz

theorem integerPolynomial_padicCongruenceProbability_tendsto_zero {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) :
    Tendsto (fun e => (Measure.pi (fun _ : Fin n => padicProbabilityHaar p))
      (padicCongruenceEvent p (MvPolynomial.map (Int.castRingHom ℤ_[p]) f) e)) atTop (𝓝 0) :=
  padicCongruenceProbability_tendsto_zero p _ (integerPolynomial_map_padic_ne_zero p hf)

end Hindman168
