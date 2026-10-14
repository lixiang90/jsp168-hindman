import Hindman168.MasterSmallPrimeExponent
import Hindman168.FiniteEventComparison

/-!
# Small-prime exceptions vanish under the actual prime-pool law

The integer divisibility event is invariant under reduction modulo any
multiple of the relevant prime powers. The independent residue product
law is therefore compared to the uniform primitive law with at most n
times the one-coordinate L1 error. For the chosen common exponent, the
actual master-stage exception probability is at most (n+1)/(w+1).
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem natCast_mod_divisor {Q q : ℕ} (h : q ∣ Q) (a : ℕ) :
    ((a % Q : ℕ) : ZMod q) = (a : ZMod q) := by
  have hh := congrArg (ZMod.castHom h (ZMod q)) (ZMod.natCast_mod a Q)
  simpa only [map_natCast] using hh

theorem integerPolynomialDivisibilityEvent_mod {Q q : ℕ} (h : q ∣ Q) {n : ℕ}
    (D : Finset (MvPolynomial (Fin n) ℤ)) (x : Fin n → ℕ) :
    integerPolynomialDivisibilityEvent q D (fun i => x i % Q) ↔
      integerPolynomialDivisibilityEvent q D x := by
  rw [integerPolynomialDivisibilityEvent_iff, integerPolynomialDivisibilityEvent_iff]
  have hx : (fun i => ((x i % Q : ℕ) : ZMod q)) = (fun i => (x i : ZMod q)) := by
    funext i
    exact natCast_mod_divisor h (x i)
  rw [hx]

noncomputable def primeSmallPrimeDivisibilityProbability {n : ℕ} (A B w : ℕ)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (e : ℕ) : ℝ :=
  event (piMass (fun _ : Fin n => primePoolMass A B))
    (fun x => ∃ p ∈ smallPrimeLabels w, integerPolynomialDivisibilityEvent (p.val ^ e) D x)

theorem primeSmallPrimeDivisibilityProbability_nonneg {n : ℕ} (A B w : ℕ)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (e : ℕ) :
    0 ≤ primeSmallPrimeDivisibilityProbability A B w D e :=
  event_nonneg _ _ (piMass_nonneg _ (fun _ => primePoolMass_nonneg A B))

theorem primeSmallPrimeDivisibilityProbability_residue {n : ℕ} (Q A B w : ℕ)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (e : ℕ) (hdiv : (primorial w) ^ e ∣ Q) :
    primeSmallPrimeDivisibilityProbability A B w D e =
      event (piMass (fun _ : Fin n => primePoolResidueMass Q A B))
        (fun x => ∃ p ∈ smallPrimeLabels w, integerPolynomialDivisibilityEvent (p.val ^ e) D x) := by
  let E : (Fin n → ℕ) → Prop :=
    fun x => ∃ p ∈ smallPrimeLabels w, integerPolynomialDivisibilityEvent (p.val ^ e) D x
  have he : (fun x => E (fun i => x i % Q)) = E := by
    funext x
    apply propext
    apply exists_congr
    intro p
    apply and_congr_right
    intro hp
    exact integerPolynomialDivisibilityEvent_mod
      ((pow_dvd_pow_of_dvd (p.property.dvd_primorial_iff.mpr
        ((smallPrimeLabels_mem w p).mp hp)) e).trans hdiv) D x
  have hm := event_map (piMass (fun _ : Fin n => primePoolMass A B))
    (fun (x : Fin n → ℕ) i => x i % Q) E
  rw [piMass_map (fun _ : Fin n => primePoolMass A B) (fun _ (a : ℕ) => a % Q), he] at hm
  exact hm.symm

theorem primeSmallPrimeDivisibilityProbability_comparison {n : ℕ} (Q A B w : ℕ)
    (hQ : 0 < Q) (hH : 0 < primePoolHarmonicMass A B)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (e : ℕ) (hdiv : (primorial w) ^ e ∣ Q) :
    |primeSmallPrimeDivisibilityProbability A B w D e - smallPrimeDivisibilityProbability Q w D e| ≤
      (n : ℝ) * distance (primePoolResidueMass Q A B) (primeUnitUniformMass Q) := by
  rw [primeSmallPrimeDivisibilityProbability_residue Q A B w D e hdiv]
  exact piMass_constant_probability_event_difference n _ _
    (primePoolResidueMass_nonneg Q A B) (primeUnitUniformMass_nonneg Q)
    (primePoolResidueMass_total Q hH) (primeUnitUniformMass_total hQ) _

theorem masterStage_smallPrime_actual_probability_le {n : ℕ}
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (w : ℕ) (M : ℕ+) (history : MasterPrimeHistory) :
    primeSmallPrimeDivisibilityProbability
      (masterStagePool w (masterSmallPrimeExponent D hD w) M history).lower
      (masterStagePool w (masterSmallPrimeExponent D hD w) M history).upper w D
      (masterSmallPrimeExponent D hD w) ≤
        1 / ((w : ℝ) + 1) + (n : ℝ) / (primePoolGrowthTarget (masterStageAuxiliary M history) w : ℝ) := by
  let e := masterSmallPrimeExponent D hD w
  let V := masterStageAuxiliary M history
  let Q := masterStageModulus w e V
  let P := masterStagePool w e M history
  have hQ : 0 < Q := masterStageModulus_pos _ _ _
  have hb := equidistributedGrowingPrimePool_bounds V Q w hQ
  have hc := primeSmallPrimeDivisibilityProbability_comparison Q P.lower P.upper w hQ
    hb.2.2.2.1 D e (dvd_mul_right _ _)
  have hu := masterStage_smallPrime_probability_lt D hD w V
  have hd : (n : ℝ) * distance (primePoolResidueMass Q P.lower P.upper) (primeUnitUniformMass Q) ≤
      (n : ℝ) / (primePoolGrowthTarget V w : ℝ) := by
    simpa only [P, masterStagePool, Q, V, div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hb.2.2.2.2 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hc' := (le_abs_self _).trans (hc.trans hd)
  change primeSmallPrimeDivisibilityProbability P.lower P.upper w D e ≤ _
  linarith

theorem masterStage_smallPrime_actual_probability_bound {n : ℕ}
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (w : ℕ) (M : ℕ+) (history : MasterPrimeHistory) :
    primeSmallPrimeDivisibilityProbability
      (masterStagePool w (masterSmallPrimeExponent D hD w) M history).lower
      (masterStagePool w (masterSmallPrimeExponent D hD w) M history).upper w D
      (masterSmallPrimeExponent D hD w) ≤ ((n : ℝ) + 1) / ((w : ℝ) + 1) := by
  have ht : w + 1 ≤ primePoolGrowthTarget (masterStageAuxiliary M history) w := by
    have hp : 1 ≤ (masterStageAuxiliary M history + 1) ^ w := one_le_pow₀ (by omega)
    simpa only [Nat.mul_one, primePoolGrowthTarget] using Nat.mul_le_mul_left (w + 1) hp
  have htr : (w : ℝ) + 1 ≤ (primePoolGrowthTarget (masterStageAuxiliary M history) w : ℝ) := by
    exact_mod_cast ht
  have hdiv : (n : ℝ) / (primePoolGrowthTarget (masterStageAuxiliary M history) w : ℝ) ≤
      (n : ℝ) / ((w : ℝ) + 1) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) htr
  calc
    _ ≤ 1 / ((w : ℝ) + 1) + (n : ℝ) / (primePoolGrowthTarget (masterStageAuxiliary M history) w : ℝ) :=
      masterStage_smallPrime_actual_probability_le D hD w M history
    _ ≤ 1 / ((w : ℝ) + 1) + (n : ℝ) / ((w : ℝ) + 1) := add_le_add le_rfl hdiv
    _ = _ := by ring

theorem masterStage_smallPrime_actual_probability_tendsto {n : ℕ}
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (M : ℕ → ℕ+) (history : ℕ → MasterPrimeHistory) :
    Tendsto (fun w => primeSmallPrimeDivisibilityProbability
      (masterStagePool w (masterSmallPrimeExponent D hD w) (M w) (history w)).lower
      (masterStagePool w (masterSmallPrimeExponent D hD w) (M w) (history w)).upper w D
      (masterSmallPrimeExponent D hD w)) atTop (𝓝 0) := by
  have ht := (tendsto_one_div_add_atTop_nhds_zero_nat
    (𝕜 := ℝ)).const_mul ((n : ℝ) + 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero, div_eq_mul_inv, one_mul] using ht)
  · exact fun w => primeSmallPrimeDivisibilityProbability_nonneg _ _ _ D _
  · exact fun w => masterStage_smallPrime_actual_probability_bound D hD w (M w) (history w)

end Hindman168
