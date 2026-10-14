import Hindman168.WeightedSchwartzZippel
import Hindman168.EquidistributedPrimePool

/-!
# Polynomial zeros and repeated variables in actual prime samples

All coordinates are independently sampled with probability proportional
to 1/p from the complete finite pool. Finite nonzero polynomial families
and repeated entries have rapidly small probabilities in the constructed
growing pools. No uniform-weight approximation is used in these bounds.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def primeIndependentMass (n A B : ℕ) : Mass (Fin n → ℕ) :=
  piMass (fun _ => primePoolMass A B)

theorem primeIndependentMass_nonneg (n A B : ℕ) (x : Fin n → ℕ) :
    0 ≤ primeIndependentMass n A B x :=
  piMass_nonneg _ (fun _ => primePoolMass_nonneg A B) x

theorem primeIndependentMass_total {n A B : ℕ} (hH : 0 < primePoolHarmonicMass A B) :
    total (primeIndependentMass n A B) = 1 :=
  piMass_total_one _ (fun _ => primePoolMass_total hH)

noncomputable def primePolynomialZeroMass {n : ℕ} (A B : ℕ)
    (p : MvPolynomial (Fin n) ℤ) : ℝ :=
  event (primeIndependentMass n A B) (fun x => MvPolynomial.eval (fun i => (x i : ℤ)) p = 0)

noncomputable def primePolynomialFamilyZeroMass {n : ℕ} (A B : ℕ)
    (D : Finset (MvPolynomial (Fin n) ℤ)) : ℝ :=
  event (primeIndependentMass n A B)
    (fun x => ∃ p ∈ D, MvPolynomial.eval (fun i => (x i : ℤ)) p = 0)

noncomputable def primeRepeatedMass (n A B : ℕ) : ℝ :=
  event (primeIndependentMass n A B) (fun x => ∃ i j, i ≠ j ∧ x i = x j)

theorem primePolynomialZeroMass_bound {n A B : ℕ} (hA : 0 < A)
    (hH : 0 < primePoolHarmonicMass A B) {p : MvPolynomial (Fin n) ℤ} (hp : p ≠ 0) :
    primePolynomialZeroMass A B p ≤
      (∑ i, (p.degreeOf i : ℝ)) * (1 / ((A : ℝ) * primePoolHarmonicMass A B)) := by
  exact weighted_schwartz_zippel_injective hp (fun _ => primePoolMass A B)
    (fun _ => primePoolMass_nonneg A B) (fun _ => primePoolMass_total hH)
    (fun x : ℕ => (x : ℤ)) Nat.cast_injective (by positivity)
    (fun _ => primePool_max_atom hA hH)

theorem primePolynomialFamilyZeroMass_bound {n A B : ℕ} (hA : 0 < A)
    (hH : 0 < primePoolHarmonicMass A B) (D : Finset (MvPolynomial (Fin n) ℤ))
    (hD : ∀ p ∈ D, p ≠ 0) :
    primePolynomialFamilyZeroMass A B D ≤
      (∑ p ∈ D, ∑ i, (p.degreeOf i : ℝ)) * (1 / ((A : ℝ) * primePoolHarmonicMass A B)) := by
  exact weighted_polynomial_family_zero_bound D hD (fun _ => primePoolMass A B)
    (fun _ => primePoolMass_nonneg A B) (fun _ => primePoolMass_total hH)
    (fun x : ℕ => (x : ℤ)) Nat.cast_injective (by positivity)
    (fun _ => primePool_max_atom hA hH)

theorem variable_difference_degree_sum_le {n : ℕ} (i j : Fin n) :
    (∑ k, ((MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin n) ℤ).degreeOf k : ℝ)) ≤ 2 := by
  calc
    _ ≤ ∑ k : Fin n, ((if k = i then 1 else 0 : ℝ) + (if k = j then 1 else 0 : ℝ)) := by
      apply Finset.sum_le_sum
      intro k _
      have hd := MvPolynomial.degreeOf_sub_le k
        (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) (MvPolynomial.X j)
      rw [MvPolynomial.degreeOf_X, MvPolynomial.degreeOf_X] at hd
      have hd' : (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin n) ℤ).degreeOf k ≤
          (if k = i then 1 else 0) + (if k = j then 1 else 0) := by
        split_ifs at * <;> omega
      exact_mod_cast hd'
    _ = 2 := by simp [Finset.sum_add_distrib]; norm_num

theorem primePairRepeatedMass_bound {n A B : ℕ} (hA : 0 < A)
    (hH : 0 < primePoolHarmonicMass A B) (i j : Fin n) :
    event (primeIndependentMass n A B) (fun x => i ≠ j ∧ x i = x j) ≤
      2 * (1 / ((A : ℝ) * primePoolHarmonicMass A B)) := by
  by_cases hij : i = j
  · subst j
    simp only [ne_eq, not_true_eq_false, false_and]
    rw [event_false]
    positivity
  · have hp : (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin n) ℤ) ≠ 0 := by
      intro hz
      exact hij (MvPolynomial.X_injective (sub_eq_zero.mp hz))
    have he := primePolynomialZeroMass_bound hA hH hp
    have heq : event (primeIndependentMass n A B) (fun x => i ≠ j ∧ x i = x j) =
        primePolynomialZeroMass A B (MvPolynomial.X i - MvPolynomial.X j) := by
      unfold primePolynomialZeroMass
      congr 1
      funext x
      simp only [MvPolynomial.eval_sub, MvPolynomial.eval_X, sub_eq_zero, Nat.cast_inj]
      exact propext (and_iff_right hij)
    rw [heq]
    exact he.trans (mul_le_mul_of_nonneg_right (variable_difference_degree_sum_le i j) (by positivity))

theorem primeRepeatedMass_bound {n A B : ℕ} (hA : 0 < A)
    (hH : 0 < primePoolHarmonicMass A B) :
    primeRepeatedMass n A B ≤ (2 * (n : ℝ) ^ 2) *
      (1 / ((A : ℝ) * primePoolHarmonicMass A B)) := by
  have he : (fun x : Fin n → ℕ => ∃ i j, i ≠ j ∧ x i = x j) =
      (fun x => ∃ ij ∈ (Finset.univ : Finset (Fin n × Fin n)), ij.1 ≠ ij.2 ∧ x ij.1 = x ij.2) := by
    funext x
    simp
  unfold primeRepeatedMass
  rw [he]
  calc
    _ ≤ ∑ ij : Fin n × Fin n, event (primeIndependentMass n A B)
        (fun x => ij.1 ≠ ij.2 ∧ x ij.1 = x ij.2) :=
      event_union_bound _ _ _ (primeIndependentMass_nonneg n A B)
    _ ≤ ∑ _ij : Fin n × Fin n, 2 * (1 / ((A : ℝ) * primePoolHarmonicMass A B)) :=
      Finset.sum_le_sum (fun ij _ => primePairRepeatedMass_bound hA hH ij.1 ij.2)
    _ = _ := by simp; ring

theorem growingPrimePolynomialFamilyZeroMass_rapid {V Q : ℕ → ℕ}
    (hQ : ∀ w, 1 ≤ Q w) (hV : ∀ᶠ w in atTop, 1 ≤ V w) {n : ℕ}
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ p ∈ D, p ≠ 0) :
    RapidlySmall atTop (fun w => (V w : ℝ)) (fun w =>
      primePolynomialFamilyZeroMass (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).lower
        (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).upper D) := by
  apply ((equidistributedGrowingPrimePool_atom_cap_rapid hQ hV).const_mul
    (∑ p ∈ D, ∑ i, (p.degreeOf i : ℝ))).of_abs_le
  apply Eventually.of_forall
  intro w
  have hn : 0 ≤ primePolynomialFamilyZeroMass
      (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).lower
      (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).upper D :=
    event_nonneg _ _ (primeIndependentMass_nonneg _ _ _)
  rw [abs_of_nonneg hn]
  exact (primePolynomialFamilyZeroMass_bound (Nat.pow_pos (by decide : 0 < 2))
    (equidistributedGrowingPrimePool_mass_pos (V w) (Q w) w (hQ w)) D hD).trans (le_abs_self _)

theorem growingPrimeRepeatedMass_rapid {V Q : ℕ → ℕ}
    (hQ : ∀ w, 1 ≤ Q w) (hV : ∀ᶠ w in atTop, 1 ≤ V w) (n : ℕ) :
    RapidlySmall atTop (fun w => (V w : ℝ)) (fun w =>
      primeRepeatedMass n (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).lower
        (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).upper) := by
  apply ((equidistributedGrowingPrimePool_atom_cap_rapid hQ hV).const_mul (2 * (n : ℝ) ^ 2)).of_abs_le
  apply Eventually.of_forall
  intro w
  have hn : 0 ≤ primeRepeatedMass n
      (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).lower
      (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).upper :=
    event_nonneg _ _ (primeIndependentMass_nonneg _ _ _)
  rw [abs_of_nonneg hn]
  exact (primeRepeatedMass_bound (Nat.pow_pos (by decide : 0 < 2))
    (equidistributedGrowingPrimePool_mass_pos (V w) (Q w) w (hQ w))).trans (le_abs_self _)

end Hindman168
