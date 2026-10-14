import Hindman168.MasterPrimePairDilation
import Hindman168.FiniteCenteredWeightedReplacement

/-! First and second moments of the actual harmonic-pool divisor mask.
The diagonal correction is kept exactly in the second-moment model.
Relative residue errors are summed with the original sampling weights. -/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def primePoolDivisorMask (A B : ℕ) (z : ℤ) : ℝ :=
  expectation (primePoolMass A B) (fun p => primeDivisorEta p z)

noncomputable def primePoolFirstMoment (A B X W : ℕ) : ℝ :=
  expectation (integerMass X W) (primePoolDivisorMask A B)

noncomputable def primePoolSecondMoment (A B X W : ℕ) : ℝ :=
  expectation (integerMass X W) (fun z => primePoolDivisorMask A B z ^ 2)

noncomputable def primePoolCenteredVariance (A B X W : ℕ) : ℝ :=
  expectation (integerMass X W) (fun z => (primePoolDivisorMask A B z - 1) ^ 2)

noncomputable def primePoolCollisionMass (A B : ℕ) : ℝ :=
  expectation (tensor (primePoolMass A B) (primePoolMass A B))
    (fun pq => if pq.1 = pq.2 then 1 else 0)

noncomputable def primePairMeanModel (pq : ℕ × ℕ) : ℝ :=
  if pq.1 = pq.2 then (pq.1 : ℝ) else 1

theorem primePoolFirstMoment_eq (A B X W : ℕ) :
    primePoolFirstMoment A B X W =
      expectation (primePoolMass A B) (fun p => total (integerEtaMass X W p)) := by
  unfold primePoolFirstMoment primePoolDivisorMask
  rw [expectation_comm]
  simp only [primeDivisorEta_expectation]

theorem primePoolSecondMoment_eq (A B X W : ℕ) :
    primePoolSecondMoment A B X W =
      expectation (tensor (primePoolMass A B) (primePoolMass A B)) (fun pq =>
        expectation (integerMass X W) (fun z => primeDivisorEta pq.1 z * primeDivisorEta pq.2 z)) := by
  unfold primePoolSecondMoment primePoolDivisorMask
  simp_rw [← expectation_independent_square]
  rw [expectation_comm]

theorem primePool_pair_diagonal_average (A B : ℕ) (f : ℕ → ℝ) :
    expectation (tensor (primePoolMass A B) (primePoolMass A B))
      (fun pq => if pq.1 = pq.2 then f pq.1 else 0) =
        ∑ p ∈ primePool A B, primePoolMass A B p ^ 2 * f p := by
  rw [expectation_eq_sum _ _ ((tensor_support _ _).trans
    (Finset.product_subset_product (primePoolMass_support A B) (primePoolMass_support A B))),
    Finset.sum_product]
  simp only [tensor_apply, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_eq_single p]
  · simp only [if_true]
    ring
  · intro q _ hqp
    rw [if_neg (Ne.symm hqp)]
  · intro hn
    exact (hn hp).elim

theorem primePoolCollisionMass_eq (A B : ℕ) :
    primePoolCollisionMass A B = ∑ p ∈ primePool A B, primePoolMass A B p ^ 2 := by
  simpa only [primePoolCollisionMass, mul_one] using primePool_pair_diagonal_average A B (fun _ => 1)

theorem primePoolCollisionMass_nonneg (A B : ℕ) : 0 ≤ primePoolCollisionMass A B := by
  rw [primePoolCollisionMass_eq]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem primePairMeanModel_average {A B : ℕ} (hS : 0 < primePoolHarmonicMass A B) :
    expectation (tensor (primePoolMass A B) (primePoolMass A B)) primePairMeanModel =
      1 + (primePoolHarmonicMass A B)⁻¹ - primePoolCollisionMass A B := by
  have he : primePairMeanModel = fun pq : ℕ × ℕ =>
      (1 + (if pq.1 = pq.2 then (pq.1 : ℝ) else 0)) - (if pq.1 = pq.2 then 1 else 0) := by
    funext pq
    unfold primePairMeanModel
    split_ifs <;> ring
  rw [he, expectation_sub, expectation_one_add, tensor_total, primePoolMass_total hS,
    one_mul, primePool_pair_diagonal_average, primePool_weighted_diagonal_identity hS]
  rfl

theorem primePoolFirstMoment_error {A B X W K : ℕ}
    (hS : 0 < primePoolHarmonicMass A B) (hX : 2 ≤ X) (hW : 0 < W)
    (hlog : (W : ℝ) / X < Real.log X)
    (hs : ∀ p ∈ primePool A B, p ≤ K ∧ W.Coprime p) :
    |primePoolFirstMoment A B X W - 1| ≤ residueError X W K := by
  have ht := primePoolMass_total hS
  rw [primePoolFirstMoment_eq, ← show expectation (primePoolMass A B) (fun _ => 1) = 1 by
    rw [expectation_const, ht, one_mul]]
  simpa only [ht, one_mul] using expectation_difference_support_bound (primePoolMass A B)
    (primePoolMass_nonneg A B) (fun p => total (integerEtaMass X W p)) (fun _ => 1)
    (residueError X W K) (fun p hp => by
      have hpool := primePoolMass_support A B hp
      exact (integerEtaMass_mass_error hX hW (primePool_mem.mp hpool).2.2.pos
        (hs p hpool).2 hlog).trans (residueError_mono hX (hs p hpool).1 hlog))

theorem primePairMeanModel_relative_error {A B X W K : ℕ}
    (hX : 2 ≤ X) (hW : 0 < W) (hlog : (W : ℝ) / X < Real.log X)
    (hs : ∀ p ∈ primePool A B, p ≤ K ∧ W.Coprime p)
    (hpair : ∀ p ∈ primePool A B, ∀ q ∈ primePool A B, p * q ≤ K)
    {p q : ℕ} (hp : p ∈ primePool A B) (hq : q ∈ primePool A B) :
    |expectation (integerMass X W) (fun z => primeDivisorEta p z * primeDivisorEta q z) -
      primePairMeanModel (p,q)| ≤ residueError X W K * primePairMeanModel (p,q) := by
  by_cases h : p = q
  · subst q
    rw [primeDivisorEta_square_expectation]
    simp only [primePairMeanModel, if_true]
    have he := (integerEtaMass_mass_error hX hW (primePool_mem.mp hp).2.2.pos
      (hs p hp).2 hlog).trans (residueError_mono hX (hs p hp).1 hlog)
    have hh := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
    have hid : (p : ℝ) * total (integerEtaMass X W p) - p =
        (p : ℝ) * (total (integerEtaMass X W p) - 1) := by ring
    rw [hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg p)]
    simpa only [mul_comm] using hh
  · simp only [primePairMeanModel, if_neg h, mul_one]
    simp_rw [primeDivisorEta_product (primePool_mem.mp hp).2.2 (primePool_mem.mp hq).2.2 h]
    rw [primeDivisorEta_expectation]
    exact (integerEtaMass_mass_error hX hW (Nat.mul_pos (primePool_mem.mp hp).2.2.pos
      (primePool_mem.mp hq).2.2.pos) ((hs p hp).2.mul_right (hs q hq).2) hlog).trans
        (residueError_mono hX (hpair p hp q hq) hlog)

theorem primePoolSecondMoment_error {A B X W K : ℕ}
    (hS : 0 < primePoolHarmonicMass A B) (hX : 2 ≤ X) (hW : 0 < W)
    (hlog : (W : ℝ) / X < Real.log X)
    (hs : ∀ p ∈ primePool A B, p ≤ K ∧ W.Coprime p)
    (hpair : ∀ p ∈ primePool A B, ∀ q ∈ primePool A B, p * q ≤ K) :
    |primePoolSecondMoment A B X W - (1 + (primePoolHarmonicMass A B)⁻¹ - primePoolCollisionMass A B)| ≤
      residueError X W K * (1 + (primePoolHarmonicMass A B)⁻¹) := by
  rw [primePoolSecondMoment_eq, ← primePairMeanModel_average hS, ← expectation_sub]
  have hb := abs_expectation_le_majorant_support (tensor (primePoolMass A B) (primePoolMass A B))
    (fun pq => expectation (integerMass X W) (fun z => primeDivisorEta pq.1 z * primeDivisorEta pq.2 z) -
      primePairMeanModel pq) (fun pq => residueError X W K * primePairMeanModel pq)
    (tensor_nonneg _ _ (primePoolMass_nonneg _ _) (primePoolMass_nonneg _ _)) (fun pq hpq => by
      have hmem := Finset.mem_product.mp (tensor_support _ _ hpq)
      exact primePairMeanModel_relative_error hX hW hlog hs hpair
        (primePoolMass_support A B hmem.1) (primePoolMass_support A B hmem.2))
  rw [expectation_const_mul, primePairMeanModel_average hS] at hb
  have he : 0 ≤ residueError X W K := by
    unfold residueError
    exact div_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg X) (sub_pos.mpr hlog).le)
  exact hb.trans (mul_le_mul_of_nonneg_left (by linarith [primePoolCollisionMass_nonneg A B]) he)

theorem primePoolCenteredVariance_eq {A B X W : ℕ} (hZ : 0 < harmonicNormalizer X W) :
    primePoolCenteredVariance A B X W =
      primePoolSecondMoment A B X W - 2 * primePoolFirstMoment A B X W + 1 := by
  have he := expectation_centered_weighted_square (integerMass X W) (fun _ => 1)
    (primePoolDivisorMask A B) 1
  simpa only [one_mul, one_pow, expectation_const, integerMass_total hZ, mul_one,
    primePoolCenteredVariance, primePoolSecondMoment, primePoolFirstMoment] using he

theorem primePoolCenteredVariance_bound {A B X W K : ℕ}
    (hS : 0 < primePoolHarmonicMass A B) (hX : 2 ≤ X) (hW : 0 < W)
    (hlog : (W : ℝ) / X < Real.log X)
    (hs : ∀ p ∈ primePool A B, p ≤ K ∧ W.Coprime p)
    (hpair : ∀ p ∈ primePool A B, ∀ q ∈ primePool A B, p * q ≤ K) :
    primePoolCenteredVariance A B X W ≤ (primePoolHarmonicMass A B)⁻¹ +
      (3 + (primePoolHarmonicMass A B)⁻¹) * residueError X W K := by
  have h₁ := (abs_le.mp (primePoolFirstMoment_error hS hX hW hlog hs)).1
  have h₂ := (abs_le.mp (primePoolSecondMoment_error hS hX hW hlog hs hpair)).2
  rw [primePoolCenteredVariance_eq (harmonicNormalizer_pos hX hW hlog)]
  linarith [primePoolCollisionMass_nonneg A B]

end Hindman168
