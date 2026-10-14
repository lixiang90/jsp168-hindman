import Hindman168.WeightedInvariantFactorCauchy

/-! Invariant-factor elimination with previous directions still averaged.
The original cell probabilities and all old Haar variables are retained. -/
namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]

theorem averaged_subgroup_invariant_factor_cauchy
    {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1)
    (f g : ι → α → G → ℝ) (C : ℝ) (hf : ∀ c u x, |f c u x| ≤ C)
    (hinv : ∀ c u x (a : Q), f c u (x + a) = f c u x) :
    (∑ c, p c * finiteHaarMean (fun u => finiteHaarMean (fun x => f c u x * g c u x))) ^ 2 ≤
      C ^ 2 * ∑ c, p c * finiteHaarMean (fun u => finiteHaarMean
        (fun x => finiteHaarMean (fun a : Q => g c u x * g c u (x + a)))) := by
  calc
    _ ≤ ∑ c, p c * (finiteHaarMean (fun u => finiteHaarMean (fun x => f c u x * g c u x))) ^ 2 :=
      probabilityWeighted_square_le p _ hp hsum
    _ ≤ ∑ c, p c * finiteHaarMean (fun u => (finiteHaarMean (fun x => f c u x * g c u x)) ^ 2) :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (finiteHaarMean_square_le _) (hp c))
    _ ≤ ∑ c, p c * finiteHaarMean (fun u => C ^ 2 * finiteHaarMean
        (fun x => finiteHaarMean (fun a : Q => g c u x * g c u (x + a)))) :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left
        (finiteHaarMean_mono _ _ (fun u =>
          subgroup_invariant_factor_cauchy Q (f c u) (g c u) C (hf c u) (hinv c u))) (hp c))
    _ = _ := by
      simp only [finiteHaarMean_const_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring

end Hindman168
