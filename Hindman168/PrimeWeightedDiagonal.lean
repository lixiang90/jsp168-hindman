import Hindman168.PrimePool
import Hindman168.ProductLaw
import Hindman168.FiniteRestrictedDomination
import Hindman168.FinitePivotCoordinates

/-! The fresh-prime diagonal retains both sampling atoms and both divisor
weights. Its mass is of order 1/S, where S is the harmonic pool mass.
An unweighted collision estimate alone does not justify deleting it. -/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def primeDivisorEta (p : ℕ) (z : ℤ) : ℝ :=
  if (p : ℤ) ∣ z then (p : ℝ) else 0

theorem primeDivisorEta_nonneg (p : ℕ) (z : ℤ) : 0 ≤ primeDivisorEta p z := by
  unfold primeDivisorEta
  split_ifs <;> positivity

theorem primeDivisorEta_expectation (X W p : ℕ) :
    expectation (integerMass X W) (primeDivisorEta p) = total (integerEtaMass X W p) := by
  rw [total_eq_sum _ (show (integerEtaMass X W p).support ⊆ (integerMass X W).support from by
    intro z hz
    apply Finsupp.mem_support_iff.mpr
    intro he
    have hh := Finsupp.mem_support_iff.mp hz
    rw [integerEtaMass_apply, he] at hh
    simp only [mul_zero, ite_self] at hh
    exact hh rfl)]
  unfold expectation Finsupp.sum
  apply Finset.sum_congr rfl
  intro z _
  rw [integerEtaMass_apply]
  simp only [primeDivisorEta, mul_ite, mul_zero]
  split_ifs <;> ring

theorem primeDivisorEta_square_expectation (X W p : ℕ) :
    expectation (integerMass X W) (fun z => primeDivisorEta p z * primeDivisorEta p z) =
      (p : ℝ) * total (integerEtaMass X W p) := by
  have he : (fun z => primeDivisorEta p z * primeDivisorEta p z) =
      fun z => (p : ℝ) * primeDivisorEta p z := by
    funext z
    unfold primeDivisorEta
    split_ifs <;> ring
  rw [he, expectation_const_mul, primeDivisorEta_expectation]

theorem primePool_weighted_diagonal_identity {A B : ℕ}
    (hS : 0 < primePoolHarmonicMass A B) :
    ∑ p ∈ primePool A B, primePoolMass A B p ^ 2 * (p : ℝ) =
      (primePoolHarmonicMass A B)⁻¹ := by
  have he (p : ℕ) (hp : p ∈ primePool A B) :
      primePoolMass A B p ^ 2 * (p : ℝ) = (p : ℝ)⁻¹ / primePoolHarmonicMass A B ^ 2 := by
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (primePool_mem.mp hp).2.2.ne_zero
    rw [primePoolMass_apply, primePoolWeight, if_pos hp]
    field_simp
  rw [Finset.sum_congr rfl he, ← Finset.sum_div]
  change primePoolHarmonicMass A B / primePoolHarmonicMass A B ^ 2 = _
  field_simp

noncomputable def primeWeightedDiagonalMass (A B X W : ℕ) : ℝ :=
  expectation (integerMass X W) (fun z =>
    expectation (tensor (primePoolMass A B) (primePoolMass A B)) (fun pq =>
      if pq.1 = pq.2 then primeDivisorEta pq.1 z * primeDivisorEta pq.2 z else 0))

theorem primeWeightedDiagonalMass_eq (A B X W : ℕ) :
    primeWeightedDiagonalMass A B X W =
      ∑ p ∈ primePool A B, primePoolMass A B p ^ 2 * (p : ℝ) * total (integerEtaMass X W p) := by
  unfold primeWeightedDiagonalMass
  rw [expectation_comm, expectation_eq_sum _ _
    ((tensor_support _ _).trans (Finset.product_subset_product
      (primePoolMass_support A B) (primePoolMass_support A B))), Finset.sum_product]
  simp only [tensor_apply]
  have he (p q : ℕ) : expectation (integerMass X W) (fun z =>
      if p = q then primeDivisorEta p z * primeDivisorEta q z else 0) =
      if p = q then (p : ℝ) * total (integerEtaMass X W p) else 0 := by
    by_cases h : p = q
    · subst q
      simp only [if_true, primeDivisorEta_square_expectation]
    · simp only [if_neg h, expectation_const, mul_zero]
  simp_rw [he]
  simp only [mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_eq_single p]
  · simp only [if_true]
    ring
  · intro q _ hqp
    rw [if_neg (Ne.symm hqp)]
  · intro hn
    exact (hn hp).elim

theorem primeWeightedDiagonalMass_bound {A B X W K : ℕ}
    (hS : 0 < primePoolHarmonicMass A B) (hX : 2 ≤ X) (hW : 0 < W)
    (hlog : (W : ℝ) / X < Real.log X)
    (hs : ∀ p ∈ primePool A B, p ≤ K ∧ W.Coprime p) :
    primeWeightedDiagonalMass A B X W ≤ (1 + residueError X W K) / primePoolHarmonicMass A B := by
  rw [primeWeightedDiagonalMass_eq]
  calc
    _ ≤ ∑ p ∈ primePool A B, (primePoolMass A B p ^ 2 * (p : ℝ)) *
        (1 + residueError X W K) := by
      apply Finset.sum_le_sum
      intro p hp
      have hm := (integerEtaMass_mass_error hX hW (primePool_mem.mp hp).2.2.pos
        (hs p hp).2 hlog).trans (residueError_mono hX (hs p hp).1 hlog)
      have ht := (abs_le.mp hm).2
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, primePool_weighted_diagonal_identity hS]
      ring

namespace FiniteMass

theorem expectation_piMass_coordinate {ι α : Type*} [Fintype ι]
    (μ : ι → Mass α) (ht : ∀ i, total (μ i) = 1) (k : ι) (f : α → ℝ) :
    expectation (piMass μ) (fun z => f (z k)) = expectation (μ k) f := by
  rw [expectation_piMass_pivot μ k]
  simp only [insertPivotCoordinate_self, expectation_const]
  rw [piMass_total_one (fun i : {i : ι // i ≠ k} => μ i.val) (fun i => ht i.val), one_mul]

end FiniteMass
end Hindman168
