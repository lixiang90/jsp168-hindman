import Hindman168.MasterReplicaCubeMeanOne

/-!
# Exact cancellation after expanding the prediction cube majorants

No independence is presumed in this algebraic step. Every subset moment
is retained under the same original joint law and the same prime event.
Its common main term cancels between the root-inserted and uninserted
products. This is the expansion used for (nu_root - 1) prod (1 + nu_row).
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def conditionalFiniteAverage {α β : Type*} (μ : Mass α)
    (base : α → Mass β) (E : α → Prop) (f : α → β → ℝ) : ℝ :=
  expectation μ (fun x => if E x then expectation (base x) (f x) else 0)

theorem conditionalFiniteAverage_sub {α β : Type*} (μ : Mass α)
    (base : α → Mass β) (E : α → Prop) (f g : α → β → ℝ) :
    conditionalFiniteAverage μ base E (fun x y => f x y - g x y) =
      conditionalFiniteAverage μ base E f - conditionalFiniteAverage μ base E g := by
  unfold conditionalFiniteAverage expectation Finsupp.sum
  simp only [mul_sub, Finset.sum_sub_distrib]
  conv_rhs => rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp [mul_sub]

theorem conditionalFiniteAverage_sum {α β ι : Type*} (μ : Mass α)
    (base : α → Mass β) (E : α → Prop) (U : Finset ι) (f : ι → α → β → ℝ) :
    conditionalFiniteAverage μ base E (fun x y => ∑ u ∈ U, f u x y) =
      ∑ u ∈ U, conditionalFiniteAverage μ base E (f u) := by
  unfold conditionalFiniteAverage expectation Finsupp.sum
  simp_rw [Finset.mul_sum, Finset.sum_comm (s := (base _).support) (t := U)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp [Finset.mul_sum]

theorem finset_product_fin_equiv {ι : Type*} (U : Finset ι) (f : ι → ℝ) :
    (∏ j : Fin (Fintype.card U), f ((Fintype.equivFin U).symm j).val) = ∏ u ∈ U, f u := by
  rw [Fintype.prod_equiv (Fintype.equivFin U).symm _ (fun u : U => f u.val) (fun _ => rfl)]
  exact Finset.prod_coe_sort U f

theorem root_majorant_product_expansion {ι : Type*} [DecidableEq ι]
    (ν : ι → ℝ) (root : ι) (U : Finset ι) (hroot : root ∉ U) :
    (ν root - 1) * ∏ u ∈ U, (1 + ν u) =
      ∑ S ∈ U.powerset, ((∏ u ∈ insert root S, ν u) - ∏ u ∈ S, ν u) := by
  rw [Finset.prod_one_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hr : root ∉ S := fun h => hroot ((Finset.mem_powerset.mp hS) h)
  rw [Finset.prod_insert hr]
  ring

theorem root_majorant_average_expansion {α β ι : Type*} [DecidableEq ι]
    (μ : Mass α) (base : α → Mass β) (E : α → Prop)
    (ν : ι → α → β → ℝ) (root : ι) (U : Finset ι) (hroot : root ∉ U) :
    conditionalFiniteAverage μ base E
      (fun x y => (ν root x y - 1) * ∏ u ∈ U, (1 + ν u x y)) =
      ∑ S ∈ U.powerset,
        (conditionalFiniteAverage μ base E (fun x y => ∏ u ∈ insert root S, ν u x y) -
          conditionalFiniteAverage μ base E (fun x y => ∏ u ∈ S, ν u x y)) := by
  have he : (fun x y => (ν root x y - 1) * ∏ u ∈ U, (1 + ν u x y)) =
      (fun x y => ∑ S ∈ U.powerset, ((∏ u ∈ insert root S, ν u x y) - ∏ u ∈ S, ν u x y)) := by
    funext x y
    exact root_majorant_product_expansion (fun u => ν u x y) root U hroot
  rw [he]
  rw [conditionalFiniteAverage_sum]
  simp_rw [conditionalFiniteAverage_sub]

theorem root_majorant_average_tendsto_zero {α β ι : Type*} [DecidableEq ι]
    (μ : ℕ → Mass α) (base : ℕ → α → Mass β) (E : ℕ → α → Prop)
    (ν : ℕ → ι → α → β → ℝ) (root : ι) (U : Finset ι) (hroot : root ∉ U)
    (k : ℕ → ℝ)
    (hmean : ∀ S : Finset ι, S ⊆ insert root U →
      Tendsto (fun w => conditionalFiniteAverage (μ w) (base w) (E w)
        (fun x y => ∏ u ∈ S, ν w u x y) - k w) atTop (𝓝 0)) :
    Tendsto (fun w => conditionalFiniteAverage (μ w) (base w) (E w)
      (fun x y => (ν w root x y - 1) * ∏ u ∈ U, (1 + ν w u x y))) atTop (𝓝 0) := by
  simp_rw [root_majorant_average_expansion _ _ _ _ root U hroot]
  have hterm (S : Finset ι) (hS : S ∈ U.powerset) :
      Tendsto (fun w => conditionalFiniteAverage (μ w) (base w) (E w)
          (fun x y => ∏ u ∈ insert root S, ν w u x y) -
        conditionalFiniteAverage (μ w) (base w) (E w)
          (fun x y => ∏ u ∈ S, ν w u x y)) atTop (𝓝 0) := by
    have hsub := Finset.mem_powerset.mp hS
    have hi := hmean (insert root S) (Finset.insert_subset_insert root hsub)
    have hs := hmean S (hsub.trans (Finset.subset_insert root U))
    convert hi.sub hs using 1 <;> simp only [sub_zero, sub_sub_sub_cancel_right]
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum U.powerset hterm

end Hindman168
