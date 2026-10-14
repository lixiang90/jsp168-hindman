import Hindman168.FiniteTensor
import Hindman168.FiniteProbability

/-!
# Genuine independent tensor probability laws

Only nonnegative total-one factors are converted into PMFs. Tensor
comparisons in FiniteTensor may have arbitrary masses. Independent
sampling and applying separate coordinate maps commute exactly.
-/

namespace Hindman168.FiniteMass

noncomputable def pairPMF {α β : Type*} (p : PMF α) (q : PMF β) : PMF (α × β) :=
  p.bind (fun a => q.map (fun b => (a, b)))

theorem pairPMF_apply {α β : Type*} (p : PMF α) (q : PMF β) (a : α) (b : β) :
    pairPMF p q (a, b) = p a * q b := by
  classical
  have hm (x : α) : (q.map (fun y => (x, y))) (a, b) = if a = x then q b else 0 := by
    rw [PMF.map_apply]
    by_cases hx : a = x
    · subst x
      simp only [Prod.mk.injEq, true_and]
      rw [tsum_eq_single b (fun y hy => if_neg (Ne.symm hy)), if_pos rfl]
      simp
    · rw [if_neg hx]
      have he (y : β) : (a, b) ≠ (x, y) := fun h => hx (congrArg Prod.fst h)
      simp only [if_neg (he _), tsum_zero]
  rw [pairPMF, PMF.bind_apply]
  simp only [hm, mul_ite, mul_zero]
  rw [tsum_eq_single a (fun x hx => if_neg (Ne.symm hx)), if_pos rfl]

theorem toPMF_tensor {α β : Type*} (μ : Mass α) (ν : Mass β)
    (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b) (htμ : total μ = 1) (htν : total ν = 1) :
    pairPMF (toPMF μ hμ htμ) (toPMF ν hν htν) =
      toPMF (tensor μ ν) (tensor_nonneg μ ν hμ hν)
        (by rw [tensor_total, htμ, htν, mul_one]) := by
  ext x
  rcases x with ⟨a, b⟩
  rw [pairPMF_apply, toPMF_apply, toPMF_apply, toPMF_apply, tensor_apply,
    ENNReal.ofReal_mul (hμ a)]

/-- Separate functions of two independent groups have independent laws. -/
theorem pairPMF_map {α β γ δ : Type*} (p : PMF α) (q : PMF β) (f : α → γ) (g : β → δ) :
    (pairPMF p q).map (fun x => (f x.1, g x.2)) = pairPMF (p.map f) (q.map g) := by
  simp only [pairPMF, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]

noncomputable def tensorListPMF {α : Type*} (μs : List (Mass α))
    (hμs : ∀ μ ∈ μs, ∀ a, 0 ≤ μ a) (ht : ∀ μ ∈ μs, total μ = 1) : PMF (List α) :=
  toPMF (tensorList μs) (tensorList_nonneg μs hμs) (tensorList_total_one μs ht)

theorem tensorListPMF_nil {α : Type*}
    (h : ∀ μ ∈ ([] : List (Mass α)), ∀ a, 0 ≤ μ a) (ht : ∀ μ ∈ ([] : List (Mass α)), total μ = 1) :
    tensorListPMF [] h ht = PMF.pure [] := by
  classical
  ext xs
  rw [tensorListPMF, toPMF_apply]
  simp only [tensorList, Finsupp.single_apply, PMF.pure_apply]
  by_cases hx : xs = []
  · subst xs; simp
  · simp [hx, Ne.symm hx]

theorem tensorListPMF_cons {α : Type*} (μ : Mass α) (μs : List (Mass α))
    (h : ∀ ν ∈ μ :: μs, ∀ a, 0 ≤ ν a) (ht : ∀ ν ∈ μ :: μs, total ν = 1) :
    tensorListPMF (μ :: μs) h ht =
      (pairPMF (toPMF μ (h μ List.mem_cons_self) (ht μ List.mem_cons_self))
        (tensorListPMF μs (fun ν hν => h ν (List.mem_cons_of_mem μ hν))
          (fun ν hν => ht ν (List.mem_cons_of_mem μ hν)))).map (fun x => x.1 :: x.2) := by
  unfold tensorListPMF
  rw [toPMF_tensor, toPMF_map]
  rfl

end Hindman168.FiniteMass
