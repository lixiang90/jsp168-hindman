import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-!
# Actual independent products of arbitrary discrete laws

The coordinate family is finite; the outcome space and the supports need
not be finite. Normalization and coordinatewise statistics follow from
the original countable sums of the product atom masses.
-/

namespace Hindman168.DiscreteProduct

open scoped BigOperators Classical ENNReal

theorem ennreal_fin_product_tsum {α : Type*} (n : ℕ) (f : Fin n → α → ℝ≥0∞) :
    (∑' x : Fin n → α, ∏ i, f i (x i)) = ∏ i, ∑' a : α, f i a := by
  induction n with
  | zero => simp
  | succ n ih =>
      let e := Fin.consEquiv (fun _ : Fin (n + 1) => α)
      rw [← e.tsum_eq (fun x => ∏ i, f i (x i)), ENNReal.tsum_prod']
      simp only [Fin.prod_univ_succ]
      change (∑' a : α, ∑' x : Fin n → α,
        f 0 a * ∏ i, f i.succ (x i)) =
          (∑' a : α, f 0 a) * ∏ i : Fin n, ∑' a : α, f i.succ a
      simp_rw [ENNReal.tsum_mul_left, ih (fun i => f i.succ)]
      rw [ENNReal.tsum_mul_right]

theorem ennreal_product_tsum {ι α : Type*} [Fintype ι] (f : ι → α → ℝ≥0∞) :
    (∑' x : ι → α, ∏ i, f i (x i)) = ∏ i, ∑' a : α, f i a := by
  classical
  let e := Fintype.equivFin ι
  let E : (Fin (Fintype.card ι) → α) ≃ (ι → α) :=
    Equiv.arrowCongr e.symm (Equiv.refl α)
  calc
    _ = ∑' x : Fin (Fintype.card ι) → α, ∏ j, f (e.symm j) (x j) := by
      rw [← E.tsum_eq (fun x => ∏ i, f i (x i))]
      apply tsum_congr
      intro x
      exact Fintype.prod_equiv e _ _ (by intro i; simp [E, Equiv.arrowCongr])
    _ = ∏ j, ∑' a : α, f (e.symm j) a := ennreal_fin_product_tsum _ _
    _ = ∏ i, ∑' a : α, f i a :=
      Fintype.prod_equiv e.symm _ _ (fun _ => rfl)

noncomputable def piPMF {ι α : Type*} [Fintype ι] (μ : ι → PMF α) : PMF (ι → α) :=
  ⟨fun x => ∏ i, μ i (x i), by
    have h : (∑' x : ι → α, ∏ i, μ i (x i)) = 1 := by
      rw [ennreal_product_tsum]
      simp only [PMF.tsum_coe, Finset.prod_const_one]
    exact h ▸ ENNReal.summable.hasSum⟩

theorem piPMF_apply {ι α : Type*} [Fintype ι] (μ : ι → PMF α) (x : ι → α) :
    piPMF μ x = ∏ i, μ i (x i) := rfl

theorem product_atom_indicator {ι α β : Type*} [Fintype ι]
    (μ : ι → PMF α) (stat : ι → α → β) (y : ι → β) (x : ι → α) :
    (if y = (fun i => stat i (x i)) then ∏ i, μ i (x i) else 0) =
      ∏ i, (if y i = stat i (x i) then μ i (x i) else 0) := by
  classical
  by_cases h : y = (fun i => stat i (x i))
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro i _
    rw [if_pos (congrFun h i)]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ stat i (x i) := by
      by_contra hn
      exact h (funext (by simpa using hn))
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm

theorem piPMF_map_coordinates {ι α β : Type*} [Fintype ι]
    (μ : ι → PMF α) (stat : ι → α → β) :
    (piPMF μ).map (fun x i => stat i (x i)) = piPMF (fun i => (μ i).map (stat i)) := by
  ext y
  rw [PMF.map_apply]
  simp only [piPMF_apply, product_atom_indicator]
  rw [ennreal_product_tsum (fun i a => if y i = stat i a then μ i a else 0)]
  simp only [PMF.map_apply]

theorem piPMF_mem_support {ι α : Type*} [Fintype ι] (μ : ι → PMF α) (x : ι → α) :
    x ∈ (piPMF μ).support ↔ ∀ i, x i ∈ (μ i).support := by
  classical
  simp only [PMF.mem_support_iff, piPMF_apply, Finset.prod_ne_zero_iff, Finset.mem_univ,
    forall_true_left]

theorem map_congr_support {α β : Type*} (μ : PMF α) (f g : α → β)
    (h : ∀ x ∈ μ.support, f x = g x) : μ.map f = μ.map g := by
  classical
  ext b
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro x
  by_cases hx : μ x = 0
  · simp only [hx, ite_self]
  · rw [h x ((PMF.mem_support_iff μ x).mpr hx)]

theorem map_equiv_apply {α β : Type*} (μ : PMF α) (e : α ≃ β) (y : β) :
    (μ.map e) y = μ (e.symm y) := by
  classical
  rw [PMF.map_apply, tsum_eq_single (e.symm y)]
  · simp
  · intro x hx
    apply if_neg
    intro h
    exact hx (by simpa using congrArg e.symm h.symm)

theorem piPMF_transpose {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (μ : ι → κ → PMF α) :
    (piPMF (fun i => piPMF (μ i))).map (fun x k i => x i k) =
      piPMF (fun k => piPMF (fun i => μ i k)) := by
  classical
  let e : (ι → κ → α) ≃ (κ → ι → α) := Equiv.piComm (fun (_ : ι) (_ : κ) => α)
  change (piPMF (fun i => piPMF (μ i))).map e = _
  ext x
  rw [map_equiv_apply]
  simp only [piPMF_apply]
  exact Finset.prod_comm

end Hindman168.DiscreteProduct
