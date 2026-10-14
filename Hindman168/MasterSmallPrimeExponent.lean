import Hindman168.UnitResidueRepresentatives
import Hindman168.MasterPrimeStage

/-!
# Actual common small-prime exponent for the master modulus

For a fixed finite nonzero integer polynomial family and prime cutoff w,
choose e0 >= 1 so that the union of p^e-divisibility events for p <= w
has probability less than any prescribed positive tolerance, for every
e >= e0. The law is the actual independent uniform primitive natural
residue law at any positive multiple of primorial(w)^e. In particular
the choice works simultaneously for all later master-stage moduli.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def primeSetDivisibilityProbability {n : ℕ} (Q : ℕ)
    (P : Finset PrimeLabel) (D : Finset (MvPolynomial (Fin n) ℤ)) (e : ℕ) : ℝ :=
  event (piMass (fun _ : Fin n => primeUnitUniformMass Q))
    (fun x => ∃ p ∈ P, integerPolynomialDivisibilityEvent (p.val ^ e) D x)

theorem primeSetDivisibilityProbability_nonneg {n : ℕ} (Q : ℕ)
    (P : Finset PrimeLabel) (D : Finset (MvPolynomial (Fin n) ℤ)) (e : ℕ) :
    0 ≤ primeSetDivisibilityProbability Q P D e :=
  event_nonneg _ _ (piMass_nonneg _ (fun _ => primeUnitUniformMass_nonneg Q))

theorem primeSetDivisibilityProbability_le_sum {n : ℕ} (Q : ℕ) (hQ : 0 < Q)
    (P : Finset PrimeLabel) (D : Finset (MvPolynomial (Fin n) ℤ)) (e : ℕ)
    (hdiv : ∀ p ∈ P, p.val ^ e ∣ Q) :
    primeSetDivisibilityProbability Q P D e ≤ ∑ p ∈ P, primeLabelUnitFamilyProbability p D e := by
  letI : NeZero Q := ⟨hQ.ne'⟩
  apply (event_union_bound _ P _ (piMass_nonneg _ (fun _ => primeUnitUniformMass_nonneg Q))).trans
  apply Finset.sum_le_sum
  intro p hp
  letI : Fact p.val.Prime := ⟨p.property⟩
  exact le_of_eq (primeUnitUniform_polynomial_divisor_probability (hdiv p hp) D)

theorem primeSetDivisibilityProbability_common_exponent {n : ℕ} (P : Finset PrimeLabel)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e0 : ℕ, 1 ≤ e0 ∧ ∀ e ≥ e0, ∀ Q : ℕ, 0 < Q →
      (∀ p ∈ P, p.val ^ e ∣ Q) → primeSetDivisibilityProbability Q P D e < ε := by
  let η : ℝ := ε / ((P.card : ℝ) + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨e0, he0⟩ := primeLabelUnitFamilyProbability_common_exponent P D hD hη
  refine ⟨max 1 e0, le_max_left _ _, ?_⟩
  intro e he Q hQ hdiv
  have he' : e0 ≤ e := (le_max_right 1 e0).trans he
  have hsum : (∑ p ∈ P, primeLabelUnitFamilyProbability p D e) ≤ (P.card : ℝ) * η := by
    calc
      _ ≤ ∑ _p ∈ P, η := Finset.sum_le_sum (fun p hp => (he0 e he' p hp).le)
      _ = (P.card : ℝ) * η := by simp
  have hprod : (P.card : ℝ) * η < ε := by
    have hmul : η * ((P.card : ℝ) + 1) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  exact lt_of_le_of_lt ((primeSetDivisibilityProbability_le_sum Q hQ P D e hdiv).trans hsum) hprod

noncomputable def smallPrimeLabels (w : ℕ) : Finset PrimeLabel :=
  (Nat.primesLE w).attach.map
    ⟨fun (p : {p : ℕ // p ∈ Nat.primesLE w}) =>
        (⟨p.val, Nat.prime_of_mem_primesLE p.property⟩ : PrimeLabel),
      fun _ _ h => Subtype.ext (congrArg (fun q : PrimeLabel => q.val) h)⟩

theorem smallPrimeLabels_mem (w : ℕ) (p : PrimeLabel) : p ∈ smallPrimeLabels w ↔ p.val ≤ w := by
  unfold smallPrimeLabels
  constructor
  · intro hp
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hp
    have hv := congrArg (fun q : PrimeLabel => q.val) ha
    exact hv ▸ Nat.le_of_mem_primesLE a.property
  · intro hp
    have ha : p.val ∈ Nat.primesLE w := Nat.mem_primesLE.mpr ⟨hp, p.property⟩
    exact Finset.mem_map.mpr ⟨⟨p.val, ha⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩

noncomputable def smallPrimeDivisibilityProbability {n : ℕ} (Q w : ℕ)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (e : ℕ) : ℝ :=
  primeSetDivisibilityProbability Q (smallPrimeLabels w) D e

theorem smallPrimeDivisibilityProbability_event {n : ℕ} (Q w : ℕ)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (e : ℕ) :
    smallPrimeDivisibilityProbability Q w D e =
      event (piMass (fun _ : Fin n => primeUnitUniformMass Q))
        (fun x => ∃ p : ℕ, p.Prime ∧ p ≤ w ∧ ∃ f ∈ D,
          ((p ^ e : ℕ) : ℤ) ∣ MvPolynomial.eval (fun i => (x i : ℤ)) f) := by
  unfold smallPrimeDivisibilityProbability primeSetDivisibilityProbability
  congr 1
  funext x
  apply propext
  constructor
  · rintro ⟨p, hp, f, hf, hzero⟩
    exact ⟨p.val, p.property, (smallPrimeLabels_mem w p).mp hp, f, hf, hzero⟩
  · rintro ⟨p, hp, hpw, f, hf, hzero⟩
    exact ⟨⟨p, hp⟩, (smallPrimeLabels_mem w ⟨p, hp⟩).mpr hpw, f, hf, hzero⟩

theorem smallPrimeDivisibilityProbability_common_exponent {n : ℕ} (w : ℕ)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e0 : ℕ, 1 ≤ e0 ∧ ∀ e ≥ e0, ∀ Q : ℕ, 0 < Q →
      (primorial w) ^ e ∣ Q → smallPrimeDivisibilityProbability Q w D e < ε := by
  obtain ⟨e0, hpos, he0⟩ := primeSetDivisibilityProbability_common_exponent (smallPrimeLabels w) D hD hε
  refine ⟨e0, hpos, ?_⟩
  intro e he Q hQ hdiv
  apply he0 e he Q hQ
  intro p hp
  exact (pow_dvd_pow_of_dvd (p.property.dvd_primorial_iff.mpr ((smallPrimeLabels_mem w p).mp hp)) e).trans hdiv

noncomputable def masterSmallPrimeExponent {n : ℕ}
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0) (w : ℕ) : ℕ :=
  (smallPrimeDivisibilityProbability_common_exponent w D hD
    (by positivity : (0 : ℝ) < 1 / ((w : ℝ) + 1))).choose

theorem masterSmallPrimeExponent_spec {n : ℕ}
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0) (w : ℕ) :
    1 ≤ masterSmallPrimeExponent D hD w ∧
      ∀ e ≥ masterSmallPrimeExponent D hD w, ∀ Q : ℕ, 0 < Q →
        (primorial w) ^ e ∣ Q → smallPrimeDivisibilityProbability Q w D e < 1 / ((w : ℝ) + 1) :=
  (smallPrimeDivisibilityProbability_common_exponent w D hD
    (by positivity : (0 : ℝ) < 1 / ((w : ℝ) + 1))).choose_spec

theorem masterStage_smallPrime_probability_lt {n : ℕ}
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0) (w V : ℕ) :
    smallPrimeDivisibilityProbability
      (masterStageModulus w (masterSmallPrimeExponent D hD w) V) w D
      (masterSmallPrimeExponent D hD w) < 1 / ((w : ℝ) + 1) := by
  apply (masterSmallPrimeExponent_spec D hD w).2 _ le_rfl _ (masterStageModulus_pos _ _ _)
  exact dvd_mul_right _ _

end Hindman168
