import Hindman168.PrimeWeightedDiagonal
import Hindman168.FiniteConvexPowerExpansion

namespace Hindman168.FiniteMass
open scoped BigOperators Classical

/-- Two distinct sampled coordinates retain the actual independent
coordinate laws, for arbitrary finite signed normalized masses. -/
theorem expectation_piMass_distinct_pair {ι A : Type*} [Fintype ι]
    (μ : ι → Mass A) (ht : ∀ i, total (μ i) = 1) (i j : ι) (hij : i ≠ j)
    (f : A → A → ℝ) :
    expectation (piMass μ) (fun s => f (s i) (s j)) =
      expectation (μ i) (fun a => expectation (μ j) (f a)) := by
  rw [expectation_piMass_pivot μ i]
  have hji : j ≠ i := Ne.symm hij
  have he (rest : {k : ι // k ≠ i} → A) (a : A) :
      insertPivotCoordinate i rest a j = rest ⟨j, hji⟩ := by
    simp only [insertPivotCoordinate, dif_neg hji]
  simp only [insertPivotCoordinate_self, he]
  rw [expectation_comm]
  simp_rw [expectation_piMass_coordinate (fun k : {k : ι // k ≠ i} => μ k.val)
    (fun k => ht k.val) ⟨j, hji⟩]

/-- The square of a centered independent sample sum has exactly m times
the original second moment. No replacement of the sample weights occurs. -/
theorem expectation_piMass_centered_sum_square {A : Type*}
    (μ : Mass A) (ht : total μ = 1) (h : A → ℝ)
    (hz : expectation μ h = 0) (m : ℕ) :
    expectation (piMass (fun _ : Fin m => μ)) (fun s => (∑ i, h (s i)) ^ 2) =
      m * expectation μ (fun a => h a ^ 2) := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, expectation_finset_sum]
  rw [Finset.sum_comm]
  have hd (i : Fin m) : expectation (piMass (fun _ : Fin m => μ))
      (fun s => h (s i) * h (s i)) = expectation μ (fun a => h a * h a) :=
    expectation_piMass_coordinate _ (fun _ => ht) i (fun a => h a * h a)
  have hoff (i j : Fin m) (hij : i ≠ j) :
      expectation (piMass (fun _ : Fin m => μ)) (fun s => h (s i) * h (s j)) = 0 := by
    rw [expectation_piMass_distinct_pair _ (fun _ => ht) i j hij (fun a b => h a * h b)]
    simp only [expectation_const_mul, hz, mul_zero, expectation_const, ht]
  have he (i : Fin m) :
      (∑ j, expectation (piMass (fun _ : Fin m => μ)) (fun s => h (s i) * h (s j))) =
        expectation μ (fun a => h a * h a) := by
    rw [Fintype.sum_eq_single i]
    · exact hd i
    · intro j hji
      exact hoff i j (Ne.symm hji)
  calc
    _ = ∑ _i : Fin m, expectation μ (fun a => h a * h a) :=
      Finset.sum_congr rfl (fun i _ => he i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Exact variance of the actual empirical mean under independent draws
from the original finite probability law. -/
theorem expectation_piMass_sample_variance {A : Type*}
    (μ : Mass A) (ht : total μ = 1) (h : A → ℝ) (m : ℕ) (hm : 0 < m) :
    expectation (piMass (fun _ : Fin m => μ))
      (fun s => ((∑ i, h (s i)) / m - expectation μ h) ^ 2) =
      (expectation μ (fun a => h a ^ 2) - expectation μ h ^ 2) / m := by
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hz : expectation μ (fun a => h a - expectation μ h) = 0 := by
    rw [expectation_sub, expectation_const, ht, one_mul, sub_self]
  have hs := expectation_piMass_centered_sum_square μ ht _ hz m
  have he (s : Fin m → A) : ((∑ i, h (s i)) / m - expectation μ h) ^ 2 =
      (m : ℝ)⁻¹ ^ 2 * (∑ i, (h (s i) - expectation μ h)) ^ 2 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp_rw [he]
  rw [expectation_const_mul, hs]
  have hv : expectation μ (fun a => (h a - expectation μ h) ^ 2) =
      expectation μ (fun a => h a ^ 2) - expectation μ h ^ 2 := by
    have hp (a : A) : (h a - expectation μ h) ^ 2 =
        h a ^ 2 - 2 * expectation μ h * h a + expectation μ h ^ 2 := by ring
    simp_rw [hp]
    rw [expectation_add, expectation_sub, expectation_const_mul, expectation_const, ht]
    ring
  rw [hv]
  field_simp

/-- Unit-bounded sample statistics have mean-square empirical error at
most 1/m, independently of the support size and its probability weights. -/
theorem expectation_piMass_sample_variance_le {A : Type*}
    (μ : Mass A) (hμ : ∀ a, 0 ≤ μ a) (ht : total μ = 1)
    (h : A → ℝ) (hh : ∀ a, |h a| ≤ 1) (m : ℕ) (hm : 0 < m) :
    expectation (piMass (fun _ : Fin m => μ))
      (fun s => ((∑ i, h (s i)) / m - expectation μ h) ^ 2) ≤ 1 / (m : ℝ) := by
  rw [expectation_piMass_sample_variance μ ht h m hm]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hb : expectation μ (fun a => h a ^ 2) ≤ 1 := by
    calc
      _ ≤ expectation μ (fun _ => (1 : ℝ)) := expectation_mono μ _ _ hμ (fun a => by
        have ha := hh a
        nlinarith [abs_nonneg (h a), sq_abs (h a)])
      _ = _ := by rw [expectation_const, ht, one_mul]
  nlinarith [sq_nonneg (expectation μ h)]

end Hindman168.FiniteMass
