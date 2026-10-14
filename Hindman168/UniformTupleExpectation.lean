import Hindman168.UniformImageHaarDensity
import Mathlib.Algebra.BigOperators.Fin

namespace Hindman168
open scoped BigOperators

theorem uniformImageTuple_expectation {S A : Type*} [Fintype S] [Nonempty S]
    [Fintype A] [Nonempty A] (d : ℕ) (e : Fin d → S → A)
    (he : ∀ j, Function.Injective (e j)) (F : (Fin d → A) → ℝ) :
    finiteHaarMean (fun v : Fin d → A => (∏ j, uniformImageHaarDensity (e j) (v j)) * F v) =
      finiteHaarMean (fun u : Fin d → S => F (fun j => e j (u j))) := by
  induction d with
  | zero =>
    simp [finiteHaarMean]
    congr 1
    exact Subsingleton.elim _ _
  | succ d ih =>
    rw [finiteHaarMean_fin_succ, finiteHaarMean_fin_succ]
    have hc (u : S) (v : Fin d → S) :
        (fun j : Fin (d + 1) => e j ((Fin.cons u v : Fin (d + 1) → S) j)) =
          Fin.cons (e 0 u) (fun j => e j.succ (v j)) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> rfl
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_assoc,
      finiteHaarMean_const_mul, hc]
    have ht (a : A) := ih (fun j => e j.succ) (fun j => he j.succ)
      (fun v => F (Fin.cons a v))
    simp only [ht]
    exact uniformImageHaarDensity_expectation (e 0) (he 0) _

theorem uniformImageTuplePair_expectation {S A : Type*} [Fintype S] [Nonempty S]
    [Fintype A] [Nonempty A] (d : ℕ) (e : Fin d → S → A)
    (he : ∀ j, Function.Injective (e j)) (F : (Fin d → A) → (Fin d → A) → ℝ) :
    finiteHaarMean (fun u : Fin d → A => finiteHaarMean (fun v : Fin d → A =>
      (∏ j, uniformImageHaarDensity (e j) (u j)) *
      (∏ j, uniformImageHaarDensity (e j) (v j)) * F u v)) =
      finiteHaarMean (fun u : Fin d → S => finiteHaarMean (fun v : Fin d → S =>
        F (fun j => e j (u j)) (fun j => e j (v j)))) := by
  simp only [mul_assoc, finiteHaarMean_const_mul, uniformImageTuple_expectation d e he]

end Hindman168
