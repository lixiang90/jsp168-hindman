import Hindman168.PositivePrincipalSumPivotConditioning

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

/-- Exact finite path partition; no independence is involved. -/
theorem principal_disjoint_event_union {α I : Type*} [Fintype I]
    (μ : Mass α) (E : I → α → Prop)
    (hd : ∀ x i j, E i x → E j x → i = j) :
    event μ (fun x => ∃ i, E i x) = ∑ i, event μ (E i) := by
  simp only [event_eq_sum _ _ (Finset.Subset.refl _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ∃ i, E i x
  · obtain ⟨i, hi⟩ := hx
    rw [if_pos ⟨i, hi⟩]
    symm
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      have hj : ¬ E j x := fun hj => hji (hd x j i hj hi)
      simp [hj]
    · simp
  · simp only [not_exists] at hx
    simp [hx]

/-- Summing arbitrary earlier path events incurs only the sum of their
error budgets. A successful extension stays within its parent path. -/
theorem principal_path_extension_sum {α I : Type*} [Fintype I]
    (μ : Mass α) (E R : I → α → Prop)
    (hd : ∀ x i j, E i x → E j x → i = j)
    (hsub : ∀ i x, R i x → E i x)
    (c : ℝ) (err : I → ℝ)
    (hstep : ∀ i, c * event μ (E i) - err i ≤ event μ (R i)) :
    c * event μ (fun x => ∃ i, E i x) - ∑ i, err i ≤
      event μ (fun x => ∃ i, R i x) := by
  rw [principal_disjoint_event_union μ E hd,
    principal_disjoint_event_union μ R (fun x i j hi hj => hd x i j (hsub i x hi) (hsub j x hj)),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum (fun i _ => hstep i)

/-- A fixed finite ordering gives actual first-success path refinement. -/
noncomputable def principalFirstSuccess {α : Type*} (N : ℕ) (P : Fin N → α → Prop)
    (x : α) : Option (Fin N) :=
  if h : (Finset.univ.filter (fun i => P i x)).Nonempty then
    some ((Finset.univ.filter (fun i => P i x)).min' h) else none

theorem principal_first_success_spec {α : Type*} (N : ℕ) (P : Fin N → α → Prop)
    (x : α) (i : Fin N) (hi : principalFirstSuccess N P x = some i) :
    P i x ∧ ∀ j, P j x → i ≤ j := by
  unfold principalFirstSuccess at hi
  split_ifs at hi with h
  · have he := Option.some.inj hi
    subst i
    exact ⟨(Finset.mem_filter.mp (Finset.min'_mem _ h)).2,
      fun j hj => Finset.min'_le (Finset.univ.filter (fun i : Fin N => P i x)) j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩

theorem principal_first_success_exists {α : Type*} (N : ℕ) (P : Fin N → α → Prop)
    (x : α) : (∃ i, principalFirstSuccess N P x = some i) ↔ ∃ i, P i x := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (principal_first_success_spec N P x i hi).1⟩
  · rintro ⟨i, hi⟩
    have h : (Finset.univ.filter (fun i => P i x)).Nonempty :=
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    simp [principalFirstSuccess, h]
end Hindman168
