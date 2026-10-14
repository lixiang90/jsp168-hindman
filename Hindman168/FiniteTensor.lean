import Hindman168.FiniteMixture
import Mathlib.Tactic.Ring

/-!
# Tensor products with the comparison-mass factors retained

These are finite signed masses, not Finsupp sup norms. Variation of a
tensor is the product of variations. The telescoping error contains
comparison-mass factors even when the original factors are probabilities.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators

noncomputable def tensor {α β : Type*} (μ : Mass α) (ν : Mass β) : Mass (α × β) := by
  classical
  exact Finsupp.onFinset (μ.support ×ˢ ν.support) (fun x => μ x.1 * ν x.2)
    (fun x hx => Finset.mem_product.mpr
      ⟨Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hx),
        Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hx)⟩)

theorem tensor_apply {α β : Type*} (μ : Mass α) (ν : Mass β) (x : α × β) :
    tensor μ ν x = μ x.1 * ν x.2 := rfl

theorem tensor_support {α β : Type*} (μ : Mass α) (ν : Mass β) :
    (tensor μ ν).support ⊆ μ.support ×ˢ ν.support := Finsupp.support_onFinset_subset

theorem tensor_nonneg {α β : Type*} (μ : Mass α) (ν : Mass β)
    (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b) (x : α × β) : 0 ≤ tensor μ ν x :=
  mul_nonneg (hμ x.1) (hν x.2)

theorem tensor_total {α β : Type*} (μ : Mass α) (ν : Mass β) :
    total (tensor μ ν) = total μ * total ν := by
  classical
  rw [total_eq_sum _ (tensor_support μ ν), Finset.sum_product]
  simp only [tensor_apply, ← Finset.mul_sum, ← Finset.sum_mul]
  rfl

theorem tensor_variation {α β : Type*} (μ : Mass α) (ν : Mass β) :
    variation (tensor μ ν) = variation μ * variation ν := by
  classical
  rw [variation_eq_sum _ (tensor_support μ ν), Finset.sum_product]
  simp only [tensor_apply, abs_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  rfl

theorem tensor_difference {α β : Type*} (μ μ' : Mass α) (ν ν' : Mass β) :
    tensor μ ν - tensor μ' ν' = tensor (μ - μ') ν + tensor μ' (ν - ν') := by
  ext x
  simp only [Finsupp.sub_apply, Finsupp.add_apply, tensor_apply]
  ring

theorem tensor_distance {α β : Type*} (μ μ' : Mass α) (ν ν' : Mass β) :
    distance (tensor μ ν) (tensor μ' ν') ≤
      distance μ μ' * variation ν + variation μ' * distance ν ν' := by
  rw [distance, tensor_difference]
  exact (variation_add _ _).trans_eq (by rw [tensor_variation, tensor_variation]; rfl)

theorem distance_nonneg {α : Type*} (μ ν : Mass α) : 0 ≤ distance μ ν := variation_nonneg _

theorem list_cons_injective {α : Type*} : Function.Injective (fun x : α × List α => x.1 :: x.2) :=
  fun _ _ h => Prod.ext (List.cons.inj h).1 (List.cons.inj h).2

noncomputable def tensorList {α : Type*} : List (Mass α) → Mass (List α)
  | [] => Finsupp.single [] 1
  | μ :: μs => (tensor μ (tensorList μs)).mapDomain (fun x => x.1 :: x.2)

theorem tensorList_apply_cons {α : Type*} (μ : Mass α) (μs : List (Mass α)) (a : α) (xs : List α) :
    tensorList (μ :: μs) (a :: xs) = μ a * tensorList μs xs := by
  rw [tensorList, Finsupp.mapDomain_apply (f := fun x : α × List α => x.1 :: x.2)
    list_cons_injective (tensor μ (tensorList μs)) (a, xs), tensor_apply]

theorem tensorList_nonneg {α : Type*} (μs : List (Mass α)) :
    (∀ μ ∈ μs, ∀ a, 0 ≤ μ a) → ∀ xs, 0 ≤ tensorList μs xs := by
  classical
  induction μs with
  | nil =>
    intro _ xs
    simp only [tensorList, Finsupp.single_apply]
    split_ifs <;> norm_num
  | cons μ μs ih =>
    intro h xs
    exact push_nonneg _ _
      (tensor_nonneg μ (tensorList μs) (h μ List.mem_cons_self)
        (ih (fun ν hν => h ν (List.mem_cons_of_mem μ hν)))) xs

theorem tensorList_total {α : Type*} (μs : List (Mass α)) :
    total (tensorList μs) = (μs.map total).prod := by
  classical
  induction μs with
  | nil => simp [tensorList, total]
  | cons μ μs ih =>
    rw [tensorList, total_push, tensor_total, ih]
    rfl

theorem tensorList_total_one {α : Type*} (μs : List (Mass α)) :
    (∀ μ ∈ μs, total μ = 1) → total (tensorList μs) = 1 := by
  classical
  induction μs with
  | nil => intro _; simp [tensorList, total]
  | cons μ μs ih =>
    intro h
    rw [tensorList, total_push, tensor_total, h μ List.mem_cons_self,
      ih (fun ν hν => h ν (List.mem_cons_of_mem μ hν)), mul_one]

theorem tensorList_variation {α : Type*} (μs : List (Mass α)) :
    variation (tensorList μs) = (μs.map variation).prod := by
  classical
  induction μs with
  | nil => simp [tensorList, variation]
  | cons μ μs ih =>
    rw [tensorList, variation_push_injective list_cons_injective, tensor_variation, ih]
    rfl

/-- The exact telescope keeps original tail variations and comparison prefix variations. -/
noncomputable def tensorError {α : Type*} : List (Mass α × Mass α) → ℝ
  | [] => 0
  | (μ, ν) :: P => distance μ ν * ((P.map Prod.fst).map variation).prod + variation ν * tensorError P

theorem tensorList_distance {α : Type*} (P : List (Mass α × Mass α)) :
    distance (tensorList (P.map Prod.fst)) (tensorList (P.map Prod.snd)) ≤ tensorError P := by
  classical
  induction P with
  | nil => simp [tensorError, distance, variation]
  | cons p P ih =>
    rcases p with ⟨μ, ν⟩
    simp only [List.map_cons, tensorList, tensorError]
    rw [distance_push_injective list_cons_injective]
    exact (tensor_distance μ ν _ _).trans (add_le_add
      (by rw [tensorList_variation]) (mul_le_mul_of_nonneg_left ih (variation_nonneg ν)))

/-- For probability originals and comparison mass <=M, a uniform error is
multiplied by the geometric sum, without normalizing comparison factors. -/
theorem tensorList_distance_uniform {α : Type*} (P : List (Mass α × Mass α)) {E M : ℝ}
    (hM : 0 ≤ M) :
    (∀ p ∈ P, (∀ a, 0 ≤ p.1 a) ∧ total p.1 = 1 ∧ (∀ a, 0 ≤ p.2 a) ∧
      total p.2 ≤ M ∧ distance p.1 p.2 ≤ E) →
    distance (tensorList (P.map Prod.fst)) (tensorList (P.map Prod.snd)) ≤
      E * ∑ i ∈ Finset.range P.length, M ^ i := by
  classical
  induction P with
  | nil => intro _; simp [distance, variation]
  | cons p P ih =>
    intro h
    rcases p with ⟨μ, ν⟩
    obtain ⟨hμ, htμ, hν, htν, hd⟩ := h (μ, ν) List.mem_cons_self
    have htail := fun q hq => h q (List.mem_cons_of_mem (μ, ν) hq)
    have htailnonneg : ∀ a, 0 ≤ tensorList (P.map Prod.fst) a := by
      apply tensorList_nonneg
      intro ρ hρ
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hρ
      exact (htail q hq).1
    have htailtotal : total (tensorList (P.map Prod.fst)) = 1 := by
      apply tensorList_total_one
      intro ρ hρ
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hρ
      exact (htail q hq).2.1
    have htv : variation (tensorList (P.map Prod.fst)) = 1 := by
      rw [variation_eq_total _ htailnonneg, htailtotal]
    have htailerror := ih htail
    have hdist0 := distance_nonneg (tensorList (P.map Prod.fst)) (tensorList (P.map Prod.snd))
    simp only [List.map_cons, tensorList, List.length_cons]
    rw [distance_push_injective list_cons_injective]
    calc
      _ ≤ distance μ ν * variation (tensorList (P.map Prod.fst)) +
          variation ν * distance (tensorList (P.map Prod.fst)) (tensorList (P.map Prod.snd)) :=
        tensor_distance _ _ _ _
      _ ≤ E + M * (E * ∑ i ∈ Finset.range P.length, M ^ i) := by
        rw [htv, mul_one, variation_eq_total ν hν]
        exact add_le_add hd (mul_le_mul htν htailerror hdist0 hM)
      _ = E * ∑ i ∈ Finset.range (P.length + 1), M ^ i := by
        rw [Finset.sum_range_succ']
        simp only [pow_succ, pow_zero, ← Finset.sum_mul]
        ring

end Hindman168.FiniteMass
