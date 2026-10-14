import Hindman168.SubgroupCubeMomentMonotone

/-! A Cauchy-Schwarz step removes a bounded factor invariant under the
averaging subgroup, leaving the exact subgroup autocorrelation. -/
namespace Hindman168
variable {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]

omit [Fintype G] in
theorem subgroupHaarMean_mul_invariant (f g : G → ℝ)
    (hf : ∀ x (a : Q), f (x + a) = f x) (x : G) :
    subgroupHaarMean Q (fun y => f y * g y) x = f x * subgroupHaarMean Q g x := by
  simp only [subgroupHaarMean, hf, finiteHaarMean_const_mul]

theorem finiteHaarMean_mul_invariant (f g : G → ℝ)
    (hf : ∀ x (a : Q), f (x + a) = f x) :
    finiteHaarMean (fun x => f x * g x) =
      finiteHaarMean (fun x => f x * subgroupHaarMean Q g x) := by
  calc
    _ = finiteHaarMean (subgroupHaarMean Q (fun x => f x * g x)) :=
      (subgroupHaarMean_integral Q _).symm
    _ = _ := congrArg finiteHaarMean (funext (subgroupHaarMean_mul_invariant Q f g hf))

theorem finiteHaarMean_discard_bounded_factor (f g : G → ℝ) (C : ℝ)
    (hf : ∀ x, |f x| ≤ C) :
    finiteHaarMean (fun x => f x * g x) ^ 2 ≤
      C ^ 2 * finiteHaarMean (fun x => g x ^ 2) := by
  have hb : finiteHaarMean (fun x => f x ^ 2) ≤ C ^ 2 := by
    calc
      _ ≤ finiteHaarMean (fun _ : G => C ^ 2) := finiteHaarMean_mono _ _
        (fun x => by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f x)) (hf x) 2)
      _ = _ := finiteHaarMean_const _
  exact (finiteHaarMean_cauchy_schwarz f g).trans
    (mul_le_mul_of_nonneg_right hb (finiteHaarMean_nonneg _ (fun x => sq_nonneg (g x))))

theorem subgroup_invariant_factor_cauchy (f g : G → ℝ) (C : ℝ)
    (hf : ∀ x, |f x| ≤ C) (hinv : ∀ x (a : Q), f (x + a) = f x) :
    finiteHaarMean (fun x => f x * g x) ^ 2 ≤
      C ^ 2 * finiteHaarMean (fun x => finiteHaarMean (fun a : Q => g x * g (x + a))) := by
  rw [finiteHaarMean_mul_invariant Q f g hinv, subgroupHaar_correlation_square Q g]
  exact finiteHaarMean_discard_bounded_factor f (subgroupHaarMean Q g) C hf

end Hindman168
