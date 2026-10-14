import Hindman168.FiniteCoordinates
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
# The coordinate product law equals the recursive list product law

The product-coordinate and recursive-list descriptions are identified as
finite masses, so this does not require any additional probabilistic axiom.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem push_const {α β : Type*} (μ : Mass α) (b : β) :
    μ.mapDomain (fun _ => b) = Finsupp.single b (total μ) := by
  ext c
  rw [push_apply, Finsupp.single_apply]
  by_cases h : c = b
  · subst c
    simp only [ite_true]
    rfl
  · simp [h, Ne.symm h]

theorem tensor_map {α β γ δ : Type*} (μ : Mass α) (ν : Mass β)
    (f : α → γ) (g : β → δ) :
    (tensor μ ν).mapDomain (fun x => (f x.1, g x.2)) =
      tensor (μ.mapDomain f) (ν.mapDomain g) := by
  ext x
  rcases x with ⟨c, d⟩
  rw [push_apply, Finset.sum_subset (tensor_support μ ν) (by
    intro p _ hp
    rw [Finsupp.notMem_support_iff.mp hp]
    split_ifs <;> rfl)]
  rw [tensor_apply, push_apply, push_apply, Finset.sum_mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [tensor_apply, Prod.mk.injEq]
  by_cases hc : c = f a <;> by_cases hd : d = g b <;> simp [hc, hd]

/-- A joint statistic of two independent coordinates is a conditional mixture. -/
theorem tensor_statistic {α β γ : Type*} (μ : Mass α) (ν : Mass β)
    (f : α → β → γ) :
    (tensor μ ν).mapDomain (fun p => f p.1 p.2) =
      mixture μ.support (fun a => μ a) (fun a => ν.mapDomain (f a)) := by
  ext c
  rw [push_apply, Finset.sum_subset (tensor_support μ ν) (by
    intro p _ hp
    rw [Finsupp.notMem_support_iff.mp hp]
    split_ifs <;> rfl)]
  rw [mixture_apply, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  rw [push_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [tensor_apply]
  split_ifs <;> simp

theorem tensor_swap {α β : Type*} (μ : Mass α) (ν : Mass β) :
    (tensor μ ν).mapDomain Prod.swap = tensor ν μ := by
  change (tensor μ ν).mapDomain (Equiv.prodComm α β) = _
  ext p
  rw [Finsupp.mapDomain_equiv_apply, tensor_apply, tensor_apply]
  exact mul_comm _ _

theorem tensor_mul_comm (μ ν : Mass ℕ) :
    (tensor μ ν).mapDomain (fun p => p.1 * p.2) =
      (tensor ν μ).mapDomain (fun p => p.1 * p.2) := by
  have h := congrArg (fun ρ : Mass (ℕ × ℕ) => ρ.mapDomain (fun p => p.1 * p.2))
    (tensor_swap μ ν)
  rw [← Finsupp.mapDomain_comp] at h
  exact (Finsupp.mapDomain_congr (fun p _ => Nat.mul_comm p.1 p.2)).trans h

theorem piMass_unit {α : Type*} (μ : Unit → Mass α) :
    (piMass μ).mapDomain (fun x => x ()) = μ () := by
  let E : (Unit → α) ≃ α :=
    ⟨fun x => x (), fun a _ => a, fun x => by funext i; cases i; rfl, fun _ => rfl⟩
  change (piMass μ).mapDomain E = _
  ext a
  rw [Finsupp.mapDomain_equiv_apply, piMass_apply]
  simp [E]

theorem piMass_fin_succ {n : ℕ} {α : Type*} (μ : Fin (n + 1) → Mass α) :
    (piMass μ).mapDomain (fun x => (x 0, fun i : Fin n => x i.succ)) =
      tensor (μ 0) (piMass (fun i : Fin n => μ i.succ)) := by
  let E := (Fin.consEquiv (fun _ : Fin (n + 1) => α)).symm
  change (piMass μ).mapDomain E = _
  ext x
  rw [Finsupp.mapDomain_equiv_apply, piMass_apply, tensor_apply, piMass_apply,
    Fin.prod_univ_succ]
  simp [E]

/-- Lists of coordinate samples have exactly the previously constructed
recursive tensor law. This equality also holds for signed component masses. -/
theorem piMass_ofFn {n : ℕ} {α : Type*} (μ : Fin n → Mass α) :
    (piMass μ).mapDomain List.ofFn = tensorList (List.ofFn μ) := by
  induction n with
  | zero =>
    change (piMass μ).mapDomain (fun _ => []) = Finsupp.single [] 1
    rw [push_const, piMass_total]
    rfl
  | succ n ih =>
    rw [List.ofFn_succ, tensorList]
    have h := congrArg (fun ν : Mass (α × (Fin n → α)) =>
      ν.mapDomain (fun p => p.1 :: List.ofFn p.2)) (piMass_fin_succ μ)
    rw [← Finsupp.mapDomain_comp] at h
    have ht := congrArg (fun ν : Mass (α × List α) =>
      ν.mapDomain (fun p => p.1 :: p.2))
      (tensor_map (μ 0) (piMass (fun i : Fin n => μ i.succ)) id List.ofFn)
    rw [← Finsupp.mapDomain_comp, Finsupp.mapDomain_id, ih] at ht
    exact (Finsupp.mapDomain_congr (fun x _ => List.ofFn_succ (f := x))).trans (h.trans ht)

end Hindman168.FiniteMass
