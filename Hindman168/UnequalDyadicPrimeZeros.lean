import Hindman168.PrimeHarmonicLower
import Hindman168.WeightedSchwartzZippel
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Polynomial zero bounds uniform in unequal dyadic endpoints

Every coordinate keeps its own normalized harmonic prime law. The degree
bound is independent of endpoint ratios.
The common threshold for dyadic exponents is proved from the retained
PNT input. This is the zero-event part of rough coprimality; it does not
claim the common-large-prime-divisor estimate.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem primePool_max_atom_log_bound {A : ℕ} (hA : 2 ≤ A)
    (hH : 1 / (8 * Real.log (A : ℝ)) ≤ primePoolHarmonicMass A (2 * A)) (p : ℕ) :
    primePoolMass A (2 * A) p ≤ 8 * Real.log (A : ℝ) / A := by
  have hAr : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hlog : 0 < Real.log (A : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < A))
  have h8log : 0 < 8 * Real.log (A : ℝ) := mul_pos (by norm_num) hlog
  have hHpos : 0 < primePoolHarmonicMass A (2 * A) :=
    (one_div_pos.mpr h8log).trans_le hH
  have hrec : 1 / primePoolHarmonicMass A (2 * A) ≤ 8 * Real.log (A : ℝ) := by
    apply (div_le_iff₀ hHpos).mpr
    have hh := (div_le_iff₀ h8log).mp hH
    simpa only [mul_comm] using hh
  calc
    _ ≤ 1 / ((A : ℝ) * primePoolHarmonicMass A (2 * A)) :=
      primePool_max_atom (by omega) hHpos p
    _ = (1 / primePoolHarmonicMass A (2 * A)) / A := by
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hrec hAr.le

theorem log_div_uniform_endpoint {L A : ℕ}
    (hL : Real.exp 1 ≤ (L : ℝ)) (hLA : L ≤ A) :
    Real.log (A : ℝ) / A ≤ Real.log (L : ℝ) / L :=
  Real.log_div_self_antitoneOn hL
    (hL.trans (by exact_mod_cast hLA)) (by exact_mod_cast hLA)

noncomputable def unequalDyadicPrimeMass {n : ℕ} (e : Fin n → ℕ) : Mass (Fin n → ℕ) :=
  piMass (fun i => primePoolMass (2 ^ e i) (2 ^ (e i + 1)))

theorem unequalDyadicPrimeMass_nonneg {n : ℕ} (e : Fin n → ℕ) (x : Fin n → ℕ) :
    0 ≤ unequalDyadicPrimeMass e x :=
  piMass_nonneg _ (fun _ => primePoolMass_nonneg _ _) x

theorem unequalDyadicPrimeMass_total {n : ℕ} (e : Fin n → ℕ)
    (hH : ∀ i, 0 < primePoolHarmonicMass (2 ^ e i) (2 ^ (e i + 1))) :
    total (unequalDyadicPrimeMass e) = 1 :=
  piMass_total_one _ (fun i => primePoolMass_total (hH i))

theorem unequalDyadicPrime_polynomial_zero_bound {n L : ℕ} (e : Fin n → ℕ)
    (hL : Real.exp 1 ≤ (L : ℝ)) (hLA : ∀ i, L ≤ 2 ^ e i)
    (hA : ∀ i, 2 ≤ 2 ^ e i)
    (hH : ∀ i, 1 / (8 * Real.log (2 ^ e i : ℕ)) ≤
      primePoolHarmonicMass (2 ^ e i) (2 ^ (e i + 1)))
    {f : MvPolynomial (Fin n) ℤ} (hf : f ≠ 0) :
    event (unequalDyadicPrimeMass e)
      (fun x => MvPolynomial.eval (fun i => (x i : ℤ)) f = 0) ≤
        (8 * ∑ i, (f.degreeOf i : ℝ)) * (Real.log (L : ℝ) / L) := by
  have hLone : 1 < (L : ℝ) := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hb : 0 ≤ 8 * (Real.log (L : ℝ) / L) :=
    mul_nonneg (by norm_num) (div_nonneg (Real.log_pos hLone).le hLpos.le)
  have hHpos : ∀ i, 0 < primePoolHarmonicMass (2 ^ e i) (2 ^ (e i + 1)) := by
    intro i
    have hlog : 0 < Real.log (2 ^ e i : ℕ) :=
      Real.log_pos (by exact_mod_cast (by have := hA i; omega : 1 < 2 ^ e i))
    exact (one_div_pos.mpr (mul_pos (by norm_num) hlog)).trans_le (hH i)
  have hcap : ∀ i p, primePoolMass (2 ^ e i) (2 ^ (e i + 1)) p ≤
      8 * (Real.log (L : ℝ) / L) := by
    intro i p
    have hi := primePool_max_atom_log_bound (hA i) (by
      simpa only [Nat.pow_succ, Nat.mul_comm] using hH i) p
    calc
      _ ≤ 8 * (Real.log (2 ^ e i : ℕ) / (2 ^ e i : ℕ)) := by
        simpa only [Nat.pow_succ, Nat.mul_comm, mul_div_assoc] using hi
      _ ≤ _ := mul_le_mul_of_nonneg_left (log_div_uniform_endpoint hL (hLA i)) (by norm_num)
  have he := weighted_schwartz_zippel_injective hf
    (fun i => primePoolMass (2 ^ e i) (2 ^ (e i + 1)))
    (fun _ => primePoolMass_nonneg _ _) (fun i => primePoolMass_total (hHpos i))
    (fun x : ℕ => (x : ℤ)) Nat.cast_injective hb hcap
  calc
    _ ≤ (∑ i, (f.degreeOf i : ℝ)) * (8 * (Real.log (L : ℝ) / L)) := he
    _ = _ := by ring

theorem exists_uniform_dyadic_zero_threshold :
    ∃ e0 : ℕ, ∀ e ≥ e0, 2 ≤ 2 ^ e ∧
      1 / (8 * Real.log (2 ^ e : ℕ)) ≤ primePoolHarmonicMass (2 ^ e) (2 ^ (e + 1)) := by
  exact eventually_atTop.mp
    ((dyadic_atTop.eventually (eventually_ge_atTop 2)).and
      primePoolHarmonicMass_dyadic_eventually_lower)

theorem unequalDyadicPrime_polynomial_zero_uniform {n : ℕ}
    {f : MvPolynomial (Fin n) ℤ} (hf : f ≠ 0) :
    ∃ e0 : ℕ, ∀ (e : Fin n → ℕ), (∀ i, e0 ≤ e i) →
      ∀ L : ℕ, Real.exp 1 ≤ (L : ℝ) → (∀ i, L ≤ 2 ^ e i) →
      event (unequalDyadicPrimeMass e)
        (fun x => MvPolynomial.eval (fun i => (x i : ℤ)) f = 0) ≤
          (8 * ∑ i, (f.degreeOf i : ℝ)) * (Real.log (L : ℝ) / L) := by
  obtain ⟨e0, he0⟩ := exists_uniform_dyadic_zero_threshold
  exact ⟨e0, fun e he L hL hLA => unequalDyadicPrime_polynomial_zero_bound e hL hLA
    (fun i => (he0 (e i) (he i)).1) (fun i => (he0 (e i) (he i)).2) hf⟩

end Hindman168
