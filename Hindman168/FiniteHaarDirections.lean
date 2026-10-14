import Hindman168.FiniteHaarIdentities
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace Hindman168
open scoped BigOperators

theorem finiteHaarMean_prod {α β : Type*} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    finiteHaarMean f = finiteHaarMean (fun a => finiteHaarMean (fun b => f (a,b))) := by
  unfold finiteHaarMean
  rw [← Finset.univ_product_univ, Finset.sum_product, Fintype.card_prod, Nat.cast_mul]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  ring

theorem finiteHaarMean_fin_succ {α : Type*} [Fintype α] (d : ℕ)
    (f : (Fin (d + 1) → α) → ℝ) :
    finiteHaarMean f = finiteHaarMean (fun a => finiteHaarMean (fun v : Fin d → α => f (Fin.cons a v))) := by
  calc
    _ = finiteHaarMean (fun p : α × (Fin d → α) => f (Fin.cons p.1 p.2)) :=
      (finiteHaarMean_equiv (Fin.consEquiv (fun _ : Fin (d + 1) => α)) f).symm
    _ = _ := finiteHaarMean_prod _

theorem finiteHaarMean_rotate {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    finiteHaarMean (fun a => finiteHaarMean (fun b => finiteHaarMean (f a b))) =
      finiteHaarMean (fun c => finiteHaarMean (fun a => finiteHaarMean (fun b => f a b c))) := by
  calc
    _ = finiteHaarMean (fun a => finiteHaarMean (fun c => finiteHaarMean (fun b => f a b c))) := by
      congr 1
      funext a
      exact finiteHaarMean_comm _
    _ = _ := finiteHaarMean_comm _

end Hindman168

