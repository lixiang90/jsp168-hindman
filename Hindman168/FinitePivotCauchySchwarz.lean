import Hindman168.FinitePivotCoordinates

/-!
# Weighted duplication under one fixed full direction-pair law

Every direction is sampled twice from the outset. Unused second samples
are marginalized with their proved mass one. The outside joint mass keeps
all original parameters and all other direction pairs. This exact lemma
compares stages under the same full law, even when direction masses depend
on the outside parameters.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem expectation_piPairs_pivot_first {ι β : Type*} [Fintype ι]
    (ν : ι → Mass β) (k : ι) (ht : total (ν k) = 1)
    (g : ({i : ι // i ≠ k} → β × β) → β → ℝ) :
    expectation (piMass (fun i => tensor (ν i) (ν i)))
      (fun v => g (fun i => v i.val) (v k).1) =
      expectation (piMass (fun i : {i : ι // i ≠ k} => tensor (ν i.val) (ν i.val)))
        (fun rest => expectation (ν k) (g rest)) := by
  rw [expectation_piMass_pivot _ k]
  simp only [insertPivotCoordinate_rest, insertPivotCoordinate_self,
    expectation_tensor_first _ ht]

theorem expectation_piPairs_pivot_outside {ι β : Type*} [Fintype ι]
    (ν : ι → Mass β) (k : ι) (ht : total (ν k) = 1)
    (Ω : ({i : ι // i ≠ k} → β × β) → ℝ) :
    expectation (piMass (fun i => tensor (ν i) (ν i))) (fun v => Ω (fun i => v i.val)) =
      expectation (piMass (fun i : {i : ι // i ≠ k} => tensor (ν i.val) (ν i.val))) Ω := by
  rw [expectation_piMass_pivot _ k]
  simp only [insertPivotCoordinate_rest, expectation_const, tensor_total, ht, one_mul]

theorem full_pair_pivot_weighted_cauchy_schwarz {α ι β : Type*} [Fintype ι]
    (ρ : Mass α) (hρ : ∀ x, 0 ≤ ρ x) (ν : α → ι → Mass β)
    (hν : ∀ x, ∀ i, ∀ t, 0 ≤ ν x i t) (k : ι) (ht : ∀ x, total (ν x k) = 1)
    (H Ω : α → ({i : ι // i ≠ k} → β × β) → ℝ)
    (g : α → ({i : ι // i ≠ k} → β × β) → β → ℝ)
    (hbound : ∀ x rest, |H x rest| ≤ Ω x rest) :
    |expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
      (fun v => H x (fun i => v i.val) * g x (fun i => v i.val) (v k).1))| ^ 2 ≤
      expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
        (fun v => Ω x (fun i => v i.val))) *
      expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
        (fun v => Ω x (fun i => v i.val) * g x (fun i => v i.val) (v k).1 *
          g x (fun i => v i.val) (v k).2)) := by
  let δ (x : α) := piMass
    (fun i : {i : ι // i ≠ k} => tensor (ν x i.val) (ν x i.val))
  let χ := conditionalJoint ρ δ
  have hχ : ∀ p, 0 ≤ χ p := conditionalJoint_nonneg ρ δ hρ (fun x _ =>
    piMass_nonneg _ (fun i t => by
      rw [tensor_apply]
      exact mul_nonneg (hν x i.val t.1) (hν x i.val t.2)))
  have hcs := conditional_weighted_cauchy_schwarz χ hχ
    (fun p => ν p.1 k) (fun p => H p.1 p.2) (fun p => Ω p.1 p.2)
    (fun p t => g p.1 p.2 t) (fun p _ => hbound p.1 p.2)
  have hleft : expectation ρ (fun x =>
      expectation (piMass (fun i => tensor (ν x i) (ν x i)))
        (fun v => H x (fun i => v i.val) * g x (fun i => v i.val) (v k).1)) =
      expectation χ (fun p => H p.1 p.2 * expectation (ν p.1 k) (g p.1 p.2)) := by
    rw [expectation_conditionalJoint]
    apply expectation_congr_support
    intro x _
    rw [expectation_piPairs_pivot_first (ν x) k (ht x)
      (fun rest t => H x rest * g x rest t)]
    simp_rw [expectation_const_mul]
    rfl
  have hpref : expectation ρ (fun x =>
      expectation (piMass (fun i => tensor (ν x i) (ν x i)))
        (fun v => Ω x (fun i => v i.val))) = expectation χ (fun p => Ω p.1 p.2) := by
    simp_rw [expectation_piPairs_pivot_outside _ k (ht _)]
    rw [expectation_conditionalJoint]
  have hright : expectation ρ (fun x =>
      expectation (piMass (fun i => tensor (ν x i) (ν x i)))
        (fun v => Ω x (fun i => v i.val) * g x (fun i => v i.val) (v k).1 *
          g x (fun i => v i.val) (v k).2)) =
      expectation χ (fun p => expectation (tensor (ν p.1 k) (ν p.1 k))
        (fun ab => Ω p.1 p.2 * g p.1 p.2 ab.1 * g p.1 p.2 ab.2)) := by
    simp_rw [expectation_piMass_pivot _ k, insertPivotCoordinate_rest, insertPivotCoordinate_self]
    rw [expectation_conditionalJoint]
  rw [hleft, hpref, hright]
  exact hcs

end Hindman168.FiniteMass
