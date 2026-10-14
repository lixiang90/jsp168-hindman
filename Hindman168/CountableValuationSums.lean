import Hindman168.CountableProductPMF
import Hindman168.PrimeValuationGeometric
import Mathlib.Data.Fintype.BigOperators

/-!
# Uniform masses of sums of independent prime valuations

Only finitely many valuation vectors can sum to a fixed a. Their number is
at most (a+1)^b, and every such product atom is at most p^(-a).
-/

namespace Hindman168

open scoped BigOperators Classical ENNReal

theorem discrete_sumPMF_apply {ι : Type*} [Fintype ι] (μ : ι → PMF ℕ) (a : ℕ) :
    ((DiscreteProduct.piPMF μ).map (fun x => ∑ i, x i)) a =
      ∑ x ∈ Fintype.piFinset (fun _ : ι => Finset.range (a + 1)),
        if a = ∑ i, x i then ∏ i, μ i (x i) else 0 := by
  classical
  rw [PMF.map_apply]
  simp only [DiscreteProduct.piPMF_apply]
  apply tsum_eq_sum
  intro x hx
  apply if_neg
  intro hsum
  apply hx
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_range.mpr
  have h : x i ≤ ∑ j, x j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (x j)) (Finset.mem_univ i)
  omega

theorem discrete_sumPMF_atom_bound {ι : Type*} [Fintype ι]
    (μ : ι → PMF ℕ) (r : ℝ≥0∞) (hμ : ∀ i a, μ i a ≤ r ^ a) (a : ℕ) :
    ((DiscreteProduct.piPMF μ).map (fun x => ∑ i, x i)) a ≤
      ((a + 1 : ℕ) : ℝ≥0∞) ^ Fintype.card ι * r ^ a := by
  rw [discrete_sumPMF_apply]
  calc
    _ ≤ ∑ x ∈ Fintype.piFinset (fun _ : ι => Finset.range (a + 1)), r ^ a := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs with hsum
      · calc
          (∏ i, μ i (x i)) ≤ ∏ i, r ^ x i := Finset.prod_le_prod' (fun i _ => hμ i (x i))
          _ = r ^ (∑ i, x i) := Finset.prod_pow_eq_pow_sum _ _ _
          _ = r ^ a := by rw [hsum]
      · exact bot_le
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Fintype.card_piFinset, Finset.card_range,
        Finset.prod_const, Finset.card_univ, Nat.cast_pow]

noncomputable def valuationSumPMF {ι : Type*} [Fintype ι] (s : ι → ℝ)
    (hs : ∀ i, 1 < s i) (p : ℕ) (hp : 2 ≤ p) : PMF ℕ :=
  (DiscreteProduct.piPMF (fun i => primeValuationPMF (s i) (hs i) p hp)).map
    (fun x => ∑ i, x i)

theorem primeValuationPMF_atom_bound {s : ℝ} (hs : 1 < s) {p : ℕ}
    (hp : 2 ≤ p) (a : ℕ) :
    primeValuationPMF s hs p hp a ≤ (ENNReal.ofReal (p : ℝ)⁻¹) ^ a := by
  rw [primeValuationPMF_apply]
  have he : ENNReal.ofReal (((p : ℝ) ^ a)⁻¹) =
      (ENNReal.ofReal (p : ℝ)⁻¹) ^ a := by
    rw [← inv_pow, ENNReal.ofReal_pow (inv_nonneg.mpr (Nat.cast_nonneg _))]
  exact (ENNReal.ofReal_le_ofReal (primeValuationMass_le_inverse_pow hs hp a)).trans_eq he

theorem valuationSumPMF_atom_bound {ι : Type*} [Fintype ι] (s : ι → ℝ)
    (hs : ∀ i, 1 < s i) (p : ℕ) (hp : 2 ≤ p) (a : ℕ) :
    valuationSumPMF s hs p hp a ≤
      ((a + 1 : ℕ) : ℝ≥0∞) ^ Fintype.card ι * (ENNReal.ofReal (p : ℝ)⁻¹) ^ a :=
  discrete_sumPMF_atom_bound _ _ (fun i => primeValuationPMF_atom_bound (hs i) hp) a

theorem valuationSumPMF_atom_bound_toReal {ι : Type*} [Fintype ι] (s : ι → ℝ)
    (hs : ∀ i, 1 < s i) (p : ℕ) (hp : 2 ≤ p) (a : ℕ) :
    (valuationSumPMF s hs p hp a).toReal ≤
      ((a + 1 : ℕ) : ℝ) ^ Fintype.card ι * ((p : ℝ) ^ a)⁻¹ := by
  have h := ENNReal.toReal_mono (by finiteness)
    (valuationSumPMF_atom_bound s hs p hp a)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg _)), inv_pow] using h

end Hindman168
