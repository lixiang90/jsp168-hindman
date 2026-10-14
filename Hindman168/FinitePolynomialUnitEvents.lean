import Hindman168.PadicResidueProduct
import Hindman168.ZModUniformUnits

/-!
# Finite uniform unit polynomial exceptions vanish at large prime powers

The complete-grid probability is the real zero-count ratio supplied by
the Haar bridge. Restricting each coordinate to units costs at most 2,
so fixed finite families also have zero limiting probability. One common
exponent is chosen for finitely many primes under the actual unit laws.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

def finitePolynomialZeroEvent {n : ℕ} (q : ℕ) (f : MvPolynomial (Fin n) ℤ)
    (x : Fin n → ZMod q) : Prop :=
  MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom (ZMod q)) f) = 0

noncomputable def finitePolynomialFullProbability {n : ℕ} (q : ℕ) [NeZero q]
    (f : MvPolynomial (Fin n) ℤ) : ℝ :=
  event (piMass (fun _ : Fin n => uniformFintypeMass (ZMod q))) (finitePolynomialZeroEvent q f)

noncomputable def finitePolynomialUnitProbability {n : ℕ} (q : ℕ) [NeZero q]
    (f : MvPolynomial (Fin n) ℤ) : ℝ :=
  event (piMass (fun _ : Fin n => zmodUnitUniformMass q)) (finitePolynomialZeroEvent q f)

noncomputable def finitePolynomialUnitFamilyProbability {n : ℕ} (q : ℕ) [NeZero q]
    (D : Finset (MvPolynomial (Fin n) ℤ)) : ℝ :=
  event (piMass (fun _ : Fin n => zmodUnitUniformMass q))
    (fun x => ∃ f ∈ D, finitePolynomialZeroEvent q f x)

theorem finitePolynomialFullProbability_eq_count {n : ℕ} (q : ℕ) [NeZero q]
    (f : MvPolynomial (Fin n) ℤ) :
    finitePolynomialFullProbability q f = ((finitePolynomialZeros q f).card : ℝ) / (q : ℝ) ^ n := by
  rw [finitePolynomialFullProbability, piUniformFintype_event, ZMod.card]
  have heq : Finset.univ.filter (finitePolynomialZeroEvent q f) = finitePolynomialZeros q f := by
    ext x
    simp only [finitePolynomialZeros, finitePolynomialZeroEvent, Finset.mem_filter]
  rw [heq]

theorem finitePolynomialFullProbability_prime_power_tendsto {p : ℕ} [Fact p.Prime] {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) :
    Tendsto (fun e => finitePolynomialFullProbability (p ^ e) f) atTop (𝓝 0) := by
  letI : MeasurableSpace ℤ_[p] := borel ℤ_[p]
  letI : BorelSpace ℤ_[p] := ⟨rfl⟩
  have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (finitePolynomial_zero_ratio_tendsto p f hf)
  simpa only [finitePolynomialFullProbability_eq_count, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_zero, Nat.cast_pow, Function.comp_def] using ht

theorem finitePolynomialUnitProbability_nonneg {n : ℕ} (q : ℕ) [NeZero q]
    (f : MvPolynomial (Fin n) ℤ) : 0 ≤ finitePolynomialUnitProbability q f :=
  event_nonneg _ _ (piMass_nonneg _ (fun _ => zmodUnitUniformMass_nonneg q))

theorem finitePolynomialUnitProbability_prime_power_le {p : ℕ} [Fact p.Prime] {n : ℕ}
    (e : ℕ) (f : MvPolynomial (Fin n) ℤ) :
    finitePolynomialUnitProbability (p ^ e) f ≤ (2 : ℝ) ^ n * finitePolynomialFullProbability (p ^ e) f :=
  zmodPrimePowerUnits_event_le (Fact.out (p := p.Prime)) e n _

theorem finitePolynomialUnitProbability_prime_power_tendsto {p : ℕ} [Fact p.Prime] {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) :
    Tendsto (fun e => finitePolynomialUnitProbability (p ^ e) f) atTop (𝓝 0) := by
  have ht := (finitePolynomialFullProbability_prime_power_tendsto (p := p) f hf).const_mul ((2 : ℝ) ^ n)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using ht)
  · exact fun e => finitePolynomialUnitProbability_nonneg _ f
  · exact fun e => finitePolynomialUnitProbability_prime_power_le (p := p) e f

theorem finitePolynomialUnitFamilyProbability_nonneg {n : ℕ} (q : ℕ) [NeZero q]
    (D : Finset (MvPolynomial (Fin n) ℤ)) : 0 ≤ finitePolynomialUnitFamilyProbability q D :=
  event_nonneg _ _ (piMass_nonneg _ (fun _ => zmodUnitUniformMass_nonneg q))

theorem finitePolynomialUnitFamilyProbability_le_sum {n : ℕ} (q : ℕ) [NeZero q]
    (D : Finset (MvPolynomial (Fin n) ℤ)) :
    finitePolynomialUnitFamilyProbability q D ≤ ∑ f ∈ D, finitePolynomialUnitProbability q f :=
  event_union_bound _ D _ (piMass_nonneg _ (fun _ => zmodUnitUniformMass_nonneg q))

theorem finitePolynomialUnitFamilyProbability_prime_power_tendsto {p : ℕ} [Fact p.Prime] {n : ℕ}
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0) :
    Tendsto (fun e => finitePolynomialUnitFamilyProbability (p ^ e) D) atTop (𝓝 0) := by
  have ht := tendsto_finsetSum D (fun f hf => finitePolynomialUnitProbability_prime_power_tendsto (p := p) f (hD f hf))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [Finset.sum_const_zero] using ht)
    (fun e => finitePolynomialUnitFamilyProbability_nonneg _ D)
    (fun e => finitePolynomialUnitFamilyProbability_le_sum _ D)

noncomputable def primeLabelUnitFamilyProbability {n : ℕ} (q : PrimeLabel)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (e : ℕ) : ℝ := by
  letI : Fact q.val.Prime := ⟨q.property⟩
  exact finitePolynomialUnitFamilyProbability (q.val ^ e) D

theorem primeLabelUnitFamilyProbability_tendsto {n : ℕ} (q : PrimeLabel)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0) :
    Tendsto (primeLabelUnitFamilyProbability q D) atTop (𝓝 0) := by
  letI : Fact q.val.Prime := ⟨q.property⟩
  exact finitePolynomialUnitFamilyProbability_prime_power_tendsto (p := q.val) D hD

theorem primeLabelUnitFamilyProbability_common_exponent {n : ℕ} (P : Finset PrimeLabel)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ e0 : ℕ, ∀ e ≥ e0, ∀ q ∈ P, primeLabelUnitFamilyProbability q D e < η := by
  apply eventually_atTop.mp
  apply (eventually_all_finset P).mpr
  intro q _
  exact (primeLabelUnitFamilyProbability_tendsto q D hD).eventually (eventually_lt_nhds hη)

end Hindman168
