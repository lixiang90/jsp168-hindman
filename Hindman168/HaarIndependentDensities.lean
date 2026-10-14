import Hindman168.HaarDifferenceDensity
import Hindman168.FiniteHaarDirections
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

namespace Hindman168
open scoped BigOperators

theorem finiteHaarMean_pi_prod {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] (r : ι → A → ℝ) :
    finiteHaarMean (fun u : ι → A => ∏ j, r j (u j)) = ∏ j, finiteHaarMean (r j) := by
  classical
  simp only [finiteHaarMean, Finset.prod_div_distrib, ← Fintype.prod_sum,
    Fintype.card_fun, Nat.cast_pow, Finset.prod_const, Finset.card_univ]

theorem finiteHaarDifferenceDensity_pi {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup A] [Fintype A] (r : ι → A → ℝ) (a : ι → A) :
    finiteHaarDifferenceDensity (fun u : ι → A => ∏ j, r j (u j)) a =
      ∏ j, finiteHaarDifferenceDensity (r j) (a j) := by
  simpa only [finiteHaarDifferenceDensity, Pi.add_apply, Finset.prod_mul_distrib] using
    finiteHaarMean_pi_prod (fun j u => r j u * r j (u + a j))

theorem independentDifferenceDensity_bound {A : Type*} [AddCommGroup A] [Fintype A]
    (d : ℕ) (r : Fin d → A → ℝ) (hr : ∀ j u, 0 ≤ r j u)
    (ht : ∀ j, finiteHaarMean (r j) = 1) (C : ℝ) (hb : ∀ j u, r j u ≤ C)
    (a : Fin d → A) : |∏ j, finiteHaarDifferenceDensity (r j) (a j)| ≤ C ^ d := by
  rw [abs_of_nonneg (Finset.prod_nonneg (fun j _ => finiteHaarDifferenceDensity_nonneg (r j) (hr j) _))]
  calc
    _ ≤ ∏ _j : Fin d, C := Finset.prod_le_prod
      (fun j _ => finiteHaarDifferenceDensity_nonneg (r j) (hr j) _)
      (fun j _ => finiteHaarDifferenceDensity_le (r j) (hr j) (ht j) C (hb j) _)
    _ = _ := by simp

theorem independentDifferences_expectation {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup A] [Fintype A] (r : ι → A → ℝ) (F : (ι → A) → ℝ) :
    finiteHaarMean (fun u : ι → A => finiteHaarMean (fun v : ι → A =>
      (∏ j, r j (u j)) * (∏ j, r j (v j)) * F (v - u))) =
      finiteHaarMean (fun a => (∏ j, finiteHaarDifferenceDensity (r j) (a j)) * F a) := by
  rw [finiteHaarDifferenceDensity_expectation]
  simp only [finiteHaarDifferenceDensity_pi]

end Hindman168
