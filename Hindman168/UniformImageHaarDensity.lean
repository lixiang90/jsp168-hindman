import Hindman168.HaarIndependentDensities
import Mathlib.Tactic.FieldSimp

namespace Hindman168
open scoped BigOperators

noncomputable def uniformImageHaarDensity {S A : Type*} [Fintype S] [Fintype A]
    (e : S → A) (a : A) : ℝ := by
  classical
  exact if a ∈ Finset.univ.image e then (Fintype.card A : ℝ) / Fintype.card S else 0

theorem uniformImageHaarDensity_nonneg {S A : Type*} [Fintype S] [Fintype A]
    (e : S → A) (a : A) : 0 ≤ uniformImageHaarDensity e a := by
  classical
  unfold uniformImageHaarDensity
  split <;> positivity

theorem uniformImageHaarDensity_le {S A : Type*} [Fintype S] [Fintype A]
    (e : S → A) (a : A) :
    uniformImageHaarDensity e a ≤ (Fintype.card A : ℝ) / Fintype.card S := by
  classical
  unfold uniformImageHaarDensity
  split
  · exact le_rfl
  · positivity

theorem uniformImageHaarDensity_expectation {S A : Type*} [Fintype S] [Nonempty S]
    [Fintype A] [Nonempty A] (e : S → A) (he : Function.Injective e) (F : A → ℝ) :
    finiteHaarMean (fun a => uniformImageHaarDensity e a * F a) =
      finiteHaarMean (fun s => F (e s)) := by
  classical
  have ha : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold finiteHaarMean uniformImageHaarDensity
  simp only [ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter,
    ← Finset.mul_sum, Finset.sum_image he.injOn]
  field_simp

theorem uniformImageHaarDensity_total {S A : Type*} [Fintype S] [Nonempty S]
    [Fintype A] [Nonempty A] (e : S → A) (he : Function.Injective e) :
    finiteHaarMean (uniformImageHaarDensity e) = 1 := by
  simpa only [mul_one, finiteHaarMean_const] using
    uniformImageHaarDensity_expectation e he (fun _ => 1)

end Hindman168
