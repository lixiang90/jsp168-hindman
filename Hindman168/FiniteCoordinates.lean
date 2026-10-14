import Hindman168.FiniteTensor
import Hindman168.FiniteProbability
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Set

/-!
# Finite independent coordinates, reindexing and marginalization

The coordinate product is a finite signed mass with its exact product
coefficients. Discarded coordinates contribute their actual total masses;
they disappear only when those masses are one. In particular, selecting
disjoint blocks from a global independent sample requires no new
independence assumption.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

noncomputable def piMass {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ∀ i, Mass (α i)) : Mass (∀ i, α i) := by
  classical
  exact Finsupp.onFinset (Fintype.piFinset (fun i => (μ i).support))
    (fun x => ∏ i, μ i (x i)) (by
      intro x hx
      apply Fintype.mem_piFinset.mpr
      intro i
      exact Finsupp.mem_support_iff.mpr (Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ i)))

theorem piMass_apply {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ∀ i, Mass (α i)) (x : ∀ i, α i) : piMass μ x = ∏ i, μ i (x i) := rfl

theorem piMass_support {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ∀ i, Mass (α i)) :
    (piMass μ).support ⊆ Fintype.piFinset (fun i => (μ i).support) := by
  classical
  exact Finsupp.support_onFinset_subset

theorem piMass_total {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ∀ i, Mass (α i)) : total (piMass μ) = ∏ i, total (μ i) := by
  classical
  rw [total_eq_sum _ (piMass_support μ)]
  simp only [piMass_apply, total, Finsupp.sum]
  exact (Finset.prod_univ_sum _ _).symm

theorem piMass_nonneg {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ∀ i, Mass (α i)) (hμ : ∀ i a, 0 ≤ μ i a) (x : ∀ i, α i) :
    0 ≤ piMass μ x := Finset.prod_nonneg (fun i _ => hμ i (x i))

theorem piMass_total_one {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ∀ i, Mass (α i)) (ht : ∀ i, total (μ i) = 1) : total (piMass μ) = 1 := by
  rw [piMass_total]
  simp only [ht, Finset.prod_const_one]

noncomputable def piPMF {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ∀ i, Mass (α i)) (hμ : ∀ i a, 0 ≤ μ i a) (ht : ∀ i, total (μ i) = 1) :
    PMF (∀ i, α i) := toPMF (piMass μ) (piMass_nonneg μ hμ) (piMass_total_one μ ht)

theorem piPMF_apply {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ∀ i, Mass (α i)) (hμ : ∀ i a, 0 ≤ μ i a) (ht : ∀ i, total (μ i) = 1)
    (x : ∀ i, α i) : piPMF μ hμ ht x = ENNReal.ofReal (∏ i, μ i (x i)) := rfl

/-- Pulling coordinates along an equivalence preserves the exact product law. -/
theorem piMass_reindex {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (μ : ι → Mass α) (e : κ ≃ ι) :
    (piMass μ).mapDomain (fun x k => x (e k)) = piMass (fun k => μ (e k)) := by
  classical
  let E : (ι → α) ≃ (κ → α) := Equiv.arrowCongr e.symm (Equiv.refl α)
  change (piMass μ).mapDomain E = _
  ext x
  rw [Finsupp.mapDomain_equiv_apply, piMass_apply, piMass_apply]
  exact Fintype.prod_equiv e.symm _ _ (by intro i; simp [E, Equiv.arrowCongr])

/-- Split a coordinate family into its two independent subfamilies. -/
theorem piMass_sum {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (μ : (ι ⊕ κ) → Mass α) :
    (piMass μ).mapDomain (fun x => (fun i => x (Sum.inl i), fun k => x (Sum.inr k))) =
      tensor (piMass (fun i => μ (Sum.inl i))) (piMass (fun k => μ (Sum.inr k))) := by
  classical
  let E := Equiv.sumPiEquivProdPi (fun _ : ι ⊕ κ => α)
  change (piMass μ).mapDomain E = _
  ext x
  rw [Finsupp.mapDomain_equiv_apply, piMass_apply, tensor_apply, piMass_apply, piMass_apply,
    Fintype.prod_sum_type]
  rfl

/-- Marginalization keeps the mass of the coordinates being discarded. -/
theorem tensor_fst {α β : Type*} (μ : Mass α) (ν : Mass β) :
    (tensor μ ν).mapDomain Prod.fst = total ν • μ := by
  classical
  ext a
  rw [push_apply]
  rw [Finset.sum_subset (tensor_support μ ν) (by
    intro x _ hx
    rw [Finsupp.notMem_support_iff.mp hx]
    split_ifs <;> rfl)]
  rw [Finset.sum_product]
  simp only [tensor_apply, Finsupp.smul_apply, smul_eq_mul]
  by_cases ha : a ∈ μ.support
  · rw [Finset.sum_eq_single a]
    · simp only [ite_true, ← Finset.mul_sum]
      change μ a * total ν = total ν * μ a
      exact mul_comm _ _
    · intro b _ hba
      simp [Ne.symm hba]
    · exact fun h => False.elim (h ha)
  · rw [Finsupp.notMem_support_iff.mp ha, mul_zero]
    apply Finset.sum_eq_zero
    intro b hb
    have hab : a ≠ b := by intro h; exact ha (h ▸ hb)
    simp [hab]

theorem piMass_inl {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (μ : (ι ⊕ κ) → Mass α) (ht : ∀ k, total (μ (Sum.inr k)) = 1) :
    (piMass μ).mapDomain (fun x i => x (Sum.inl i)) = piMass (fun i => μ (Sum.inl i)) := by
  have h := congrArg (fun ν : Mass ((ι → α) × (κ → α)) => ν.mapDomain Prod.fst)
    (piMass_sum μ)
  rw [← Finsupp.mapDomain_comp, tensor_fst, piMass_total_one _ ht, one_smul] at h
  exact h

/-- Restriction to any injective coordinate selection is the corresponding
product probability law. The unused coordinates are integrated out. -/
theorem piMass_restrict {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (μ : ι → Mass α) (j : κ → ι) (hj : Function.Injective j)
    (ht : ∀ i, total (μ i) = 1) :
    (piMass μ).mapDomain (fun x k => x (j k)) = piMass (fun k => μ (j k)) := by
  classical
  let L := {i : ι // i ∉ Set.range j}
  let e : κ ⊕ L ≃ ι :=
    (Equiv.sumCongr (Equiv.ofInjective j hj) (Equiv.refl L)).trans
      (Equiv.sumCompl (fun i => i ∈ Set.range j))
  have he (k : κ) : e (Sum.inl k) = j k := rfl
  have h := congrArg (fun ν : Mass ((κ ⊕ L) → α) =>
    ν.mapDomain (fun x k => x (Sum.inl k))) (piMass_reindex μ e)
  rw [← Finsupp.mapDomain_comp, piMass_inl _ (fun k => ht (e (Sum.inr k)))] at h
  simpa only [Function.comp_def, he] using h

theorem piPMF_restrict {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (μ : ι → Mass α) (j : κ → ι) (hj : Function.Injective j)
    (hμ : ∀ i a, 0 ≤ μ i a) (ht : ∀ i, total (μ i) = 1) :
    (piPMF μ hμ ht).map (fun x k => x (j k)) =
      piPMF (fun k => μ (j k)) (fun k => hμ (j k)) (fun k => ht (j k)) := by
  ext x
  rw [piPMF, toPMF_map_apply, piMass_restrict μ j hj ht, piPMF, toPMF_apply]

/-- Separate coordinate maps preserve independence, even when the maps
are not injective (for example, when each block is replaced by its product). -/
theorem piMass_map {ι : Type*} [Fintype ι] {α β : ι → Type*}
    (μ : ∀ i, Mass (α i)) (f : ∀ i, α i → β i) :
    (piMass μ).mapDomain (fun x i => f i (x i)) =
      piMass (fun i => (μ i).mapDomain (f i)) := by
  classical
  ext y
  rw [push_apply]
  rw [Finset.sum_subset (piMass_support μ) (by
    intro x _ hx
    rw [Finsupp.notMem_support_iff.mp hx]
    split_ifs <;> rfl)]
  rw [piMass_apply]
  simp only [push_apply]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [piMass_apply]
  by_cases h : y = fun i => f i (x i)
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro i _
    rw [if_pos (congrFun h i)]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ f i (x i) := by
      simpa only [funext_iff, not_forall] using h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm

/-- Group a sigma-indexed family into a family of independent blocks. -/
theorem piMass_group {ι : Type*} [Fintype ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] {α : Type*} (μ : (Σ i, κ i) → Mass α) :
    (piMass μ).mapDomain (fun x i k => x ⟨i, k⟩) =
      piMass (fun i => piMass (fun k => μ ⟨i, k⟩)) := by
  classical
  let E := Equiv.piCurry (fun (i : ι) (_ : κ i) => α)
  change (piMass μ).mapDomain E = _
  ext x
  rw [Finsupp.mapDomain_equiv_apply, piMass_apply]
  simp only [piMass_apply]
  exact Fintype.prod_sigma _

/-- Disjoint global coordinate groups may be replaced by arbitrary block
statistics. This is derived by restriction, grouping and coordinate mapping. -/
theorem piMass_disjoint_statistics {I B α β : Type*} [Fintype I] [Fintype B]
    {κ : B → Type*} [∀ b, Fintype (κ b)]
    (μ : I → Mass α) (j : (Σ b, κ b) → I) (hj : Function.Injective j)
    (ht : ∀ i, total (μ i) = 1) (f : ∀ b, (κ b → α) → β) :
    (piMass μ).mapDomain (fun x b => f b (fun k => x (j ⟨b, k⟩))) =
      piMass (fun b => (piMass (fun k => μ (j ⟨b, k⟩))).mapDomain (f b)) := by
  have h := congrArg (fun ν : Mass ((Σ b, κ b) → α) =>
    ν.mapDomain (fun x b => f b (fun k => x ⟨b, k⟩))) (piMass_restrict μ j hj ht)
  rw [← Finsupp.mapDomain_comp] at h
  have hg := congrArg (fun ν : Mass (∀ b, κ b → α) =>
    ν.mapDomain (fun x b => f b (x b))) (piMass_group (fun p => μ (j p)))
  rw [← Finsupp.mapDomain_comp, piMass_map] at hg
  exact h.trans hg

theorem piPMF_disjoint_statistics {I B α β : Type*} [Fintype I] [Fintype B]
    {κ : B → Type*} [∀ b, Fintype (κ b)]
    (μ : I → Mass α) (j : (Σ b, κ b) → I) (hj : Function.Injective j)
    (hμ : ∀ i a, 0 ≤ μ i a) (ht : ∀ i, total (μ i) = 1)
    (f : ∀ b, (κ b → α) → β) :
    (piPMF μ hμ ht).map (fun x b => f b (fun k => x (j ⟨b, k⟩))) =
      piPMF (fun b => (piMass (fun k => μ (j ⟨b, k⟩))).mapDomain (f b))
        (fun b => push_nonneg _ _ (piMass_nonneg _ (fun k => hμ (j ⟨b, k⟩))))
        (fun b => by rw [total_push, piMass_total_one _ (fun k => ht (j ⟨b, k⟩))]) := by
  ext y
  rw [piPMF, toPMF_map_apply, piMass_disjoint_statistics μ j hj ht f, piPMF, toPMF_apply]

end Hindman168.FiniteMass
