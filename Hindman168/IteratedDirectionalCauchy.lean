import Hindman168.HaarDyadicPower
import Hindman168.SubgroupInvariantFactorCauchy
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace Hindman168
open scoped BigOperators
variable {H Q : Type*} [AddCommGroup H] [AddCommGroup Q] [Fintype H] [Fintype Q]

noncomputable def iteratedDirectionalMean :
    (n : ℕ) → (Fin n → Q →+ H) → (H → ℝ) → ℝ
  | 0, _, h => finiteHaarMean h
  | n + 1, D, h => finiteHaarMean (fun a : Q =>
      iteratedDirectionalMean n (fun j => D j.succ) (fun x => h x * h (x + D 0 a)))

theorem injectiveDirection_factor_cauchy (D : Q →+ H) (hD : Function.Injective D)
    (f g : H → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (hi : ∀ x a, f (x + D a) = f x) :
    finiteHaarMean (fun x => f x * g x) ^ 2 ≤
      finiteHaarMean (fun x => finiteHaarMean (fun a : Q => g x * g (x + D a))) := by
  classical
  letI : Fintype D.range := Fintype.ofFinite _
  have hinv (x : H) (a : D.range) : f (x + a) = f x := by
    obtain ⟨b, hb⟩ := a.property
    rw [← hb]
    exact hi x b
  have he (x : H) : finiteHaarMean (fun a : D.range => g x * g (x + a)) =
      finiteHaarMean (fun a : Q => g x * g (x + D a)) :=
    (finiteHaarMean_equiv (β := D.range) (Equiv.ofInjective D hD) _).symm
  simpa only [one_pow, one_mul, he] using subgroup_invariant_factor_cauchy D.range f g 1 hf hinv

theorem iteratedDirectionalCauchy (n : ℕ) (D : Fin n → Q →+ H)
    (hD : ∀ j, Function.Injective (D j)) (f : Fin n → H → ℝ)
    (hf : ∀ j x, |f j x| ≤ 1) (hi : ∀ j x a, f j (x + D j a) = f j x)
    (h : H → ℝ) :
    finiteHaarMean (fun x => h x * ∏ j, f j x) ^ (2 ^ n) ≤ iteratedDirectionalMean n D h := by
  induction n generalizing h with
  | zero => simp [iteratedDirectionalMean]
  | succ n ih =>
    let g : H → ℝ := fun x => h x * ∏ j : Fin n, f j.succ x
    have hbase : finiteHaarMean (fun x => h x * ∏ j : Fin (n + 1), f j x) ^ 2 ≤
        finiteHaarMean (fun a : Q => finiteHaarMean (fun x => g x * g (x + D 0 a))) := by
      have he : (fun x => h x * ∏ j : Fin (n + 1), f j x) = (fun x => f 0 x * g x) := by
        funext x
        rw [Fin.prod_univ_succ]
        dsimp [g]
        ring
      rw [he, finiteHaarMean_comm]
      exact injectiveDirection_factor_cauchy (D 0) (hD 0) (f 0) g (hf 0) (hi 0)
    have hnext (a : Q) :
        finiteHaarMean (fun x => g x * g (x + D 0 a)) ^ (2 ^ n) ≤
          iteratedDirectionalMean n (fun j => D j.succ) (fun x => h x * h (x + D 0 a)) := by
      have hb (j : Fin n) (x : H) : |f j.succ x * f j.succ (x + D 0 a)| ≤ 1 := by
        rw [abs_mul]
        exact mul_le_one₀ (hf _ _) (abs_nonneg _) (hf _ _)
      have hinv (j : Fin n) (x : H) (b : Q) :
          f j.succ (x + D j.succ b) * f j.succ (x + D j.succ b + D 0 a) =
            f j.succ x * f j.succ (x + D 0 a) := by
        rw [add_right_comm x (D j.succ b) (D 0 a), hi, hi]
      have he : (fun x => g x * g (x + D 0 a)) =
          (fun x => (h x * h (x + D 0 a)) * ∏ j : Fin n, (f j.succ x * f j.succ (x + D 0 a))) := by
        funext x
        simp only [Finset.prod_mul_distrib]
        dsimp [g]
        ring
      rw [he]
      exact ih (fun j => D j.succ) (fun j => hD j.succ)
        (fun j x => f j.succ x * f j.succ (x + D 0 a)) hb hinv _
    calc
      _ = (finiteHaarMean (fun x => h x * ∏ j, f j x) ^ 2) ^ (2 ^ n) := by
        rw [← pow_mul, pow_succ, Nat.mul_comm 2]
      _ ≤ (finiteHaarMean (fun a : Q => finiteHaarMean (fun x => g x * g (x + D 0 a)))) ^ (2 ^ n) :=
        pow_le_pow_left₀ (sq_nonneg _) hbase _
      _ ≤ finiteHaarMean (fun a : Q => finiteHaarMean (fun x => g x * g (x + D 0 a)) ^ (2 ^ n)) :=
        finiteHaarMean_pow_two_pow_le _ n
      _ ≤ _ := finiteHaarMean_mono _ _ hnext

end Hindman168
