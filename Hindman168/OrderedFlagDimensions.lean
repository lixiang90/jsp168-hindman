import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Order.Interval.Finset.Fin

namespace Hindman168
open Module

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

theorem basis_suffix_span_finrank {n : ℕ} (b : Basis (Fin n) K M) (t : ℕ) :
    Module.finrank K (Submodule.span K (b '' {i | t ≤ i.val})) = n-t := by
  classical
  let p := fun i : Fin n => t ≤ i.val
  have he : Set.range (fun i : {i : Fin n // p i} => b i.val) = b '' {i | p i} := by
    ext x
    simp
  rw [← he]
  have hd : Module.finrank K (Submodule.span K (Set.range (fun i : {i : Fin n // p i} => b i.val))) =
      Fintype.card {i : Fin n // p i} :=
    finrank_span_eq_card (b.linearIndependent.comp (fun i : {i : Fin n // p i} => i.val)
      Subtype.val_injective)
  rw [hd]
  rw [Fintype.card_subtype]
  by_cases ht : t < n
  · have hf : Finset.univ.filter p = Finset.Ici (⟨t, ht⟩ : Fin n) := by
      ext i
      simp [p, Fin.le_def]
    rw [hf, Fin.card_Ici]
  · have hp : ∀ i : Fin n, ¬ p i := fun i hi => ht (lt_of_le_of_lt hi i.isLt)
    simp only [Finset.filter_eq_empty_iff.mpr (fun i _ => hp i), Finset.card_empty,
      Nat.sub_eq_zero_of_le (Nat.le_of_not_gt ht)]

end Hindman168
