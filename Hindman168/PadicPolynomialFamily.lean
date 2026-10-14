import Hindman168.PadicResidueHaar

/-!
# Finite polynomial families and a common p-adic exception exponent

The entire finite-family bad-event probability tends to zero under each
prime's actual Haar product law. A finite collection of primes therefore
admits one common exponent for any positive tolerance. Transfer to the
uniform primitive classes modulo the master primorial is not asserted.
-/

namespace Hindman168

open MeasureTheory Filter
open scoped BigOperators Topology Classical

variable (p : ℕ) [Fact p.Prime] [MeasurableSpace ℤ_[p]] [BorelSpace ℤ_[p]]

noncomputable def padicIntegerFamilyEvent {n : ℕ} (D : Finset (MvPolynomial (Fin n) ℤ)) (e : ℕ) :
    Set (Fin n → ℤ_[p]) :=
  ⋃ f ∈ D, padicCongruenceEvent p (MvPolynomial.map (Int.castRingHom ℤ_[p]) f) e

theorem padicIntegerFamilyEvent_measurable {n : ℕ} (D : Finset (MvPolynomial (Fin n) ℤ)) (e : ℕ) :
    MeasurableSet (padicIntegerFamilyEvent p D e) :=
  MeasurableSet.biUnion D.countable_toSet (fun f _ =>
    padicCongruenceEvent_measurable p (MvPolynomial.map (Int.castRingHom ℤ_[p]) f) e)

theorem padicIntegerFamilyProbability_tendsto_zero {n : ℕ}
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0) :
    Tendsto (fun e => (Measure.pi (fun _ : Fin n => padicProbabilityHaar p))
      (padicIntegerFamilyEvent p D e)) atTop (𝓝 0) := by
  have ht := tendsto_finsetSum D (fun f hf =>
    integerPolynomial_padicCongruenceProbability_tendsto_zero p f (hD f hf))
  have ht' : Tendsto (fun e => ∑ f ∈ D, (Measure.pi (fun _ : Fin n => padicProbabilityHaar p))
      (padicCongruenceEvent p (MvPolynomial.map (Int.castRingHom ℤ_[p]) f) e)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht'
    (fun _ => zero_le) (fun e => measure_biUnion_finset_le D _)

theorem padicIntegerFamilyProbability_eventually_small {n : ℕ}
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    {η : ENNReal} (hη : 0 < η) :
    ∃ e0 : ℕ, ∀ e ≥ e0, (Measure.pi (fun _ : Fin n => padicProbabilityHaar p))
      (padicIntegerFamilyEvent p D e) < η :=
  eventually_atTop.mp ((padicIntegerFamilyProbability_tendsto_zero p D hD).eventually
    (eventually_lt_nhds hη))

abbrev PrimeLabel := {p : ℕ // p.Prime}

noncomputable def primeLabelFamilyProbability {n : ℕ} (q : PrimeLabel)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (e : ℕ) : ENNReal := by
  letI : Fact q.val.Prime := ⟨q.property⟩
  letI : MeasurableSpace ℤ_[q.val] := borel ℤ_[q.val]
  letI : BorelSpace ℤ_[q.val] := ⟨rfl⟩
  exact (Measure.pi (fun _ : Fin n => padicProbabilityHaar q.val))
    (padicIntegerFamilyEvent q.val D e)

theorem primeLabelFamilyProbability_tendsto_zero {n : ℕ} (q : PrimeLabel)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0) :
    Tendsto (primeLabelFamilyProbability q D) atTop (𝓝 0) := by
  letI : Fact q.val.Prime := ⟨q.property⟩
  letI : MeasurableSpace ℤ_[q.val] := borel ℤ_[q.val]
  letI : BorelSpace ℤ_[q.val] := ⟨rfl⟩
  exact padicIntegerFamilyProbability_tendsto_zero q.val D hD

theorem primeLabelFamilyProbability_common_exponent {n : ℕ} (P : Finset PrimeLabel)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    {η : ENNReal} (hη : 0 < η) :
    ∃ e0 : ℕ, ∀ e ≥ e0, ∀ q ∈ P, primeLabelFamilyProbability q D e < η := by
  apply eventually_atTop.mp
  apply (eventually_all_finset P).mpr
  intro q _
  exact (primeLabelFamilyProbability_tendsto_zero q D hD).eventually (eventually_lt_nhds hη)

end Hindman168
