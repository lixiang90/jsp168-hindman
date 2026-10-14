import Hindman168.FiniteMixture
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite real probabilities and actual mathlib PMFs

Finite nonnegative masses of total one define genuine PMFs. Pushforward
and conditional mixture coefficients are proved equal, including maps
that are not injective. Unnormalized comparison weights are not converted.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators

noncomputable def toPMF {α : Type*} (μ : Mass α) (hμ : ∀ a, 0 ≤ μ a)
    (ht : total μ = 1) : PMF α := by
  classical
  exact PMF.ofFinset (fun a => ENNReal.ofReal (μ a)) μ.support
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hμ a)]
      change ENNReal.ofReal (total μ) = 1
      rw [ht, ENNReal.ofReal_one])
    (by intro a ha; rw [Finsupp.notMem_support_iff.mp ha, ENNReal.ofReal_zero])

theorem toPMF_apply {α : Type*} (μ : Mass α) (hμ : ∀ a, 0 ≤ μ a)
    (ht : total μ = 1) (a : α) : toPMF μ hμ ht a = ENNReal.ofReal (μ a) := rfl

theorem toPMF_map_apply {α β : Type*} (μ : Mass α) (hμ : ∀ a, 0 ≤ μ a)
    (ht : total μ = 1) (f : α → β) (b : β) :
    (toPMF μ hμ ht).map f b = ENNReal.ofReal (μ.mapDomain f b) := by
  classical
  rw [PMF.map_apply, tsum_eq_sum (s := μ.support) (fun a ha => by
    rw [toPMF_apply, Finsupp.notMem_support_iff.mp ha]
    simp)]
  have he : ∀ a : α, (if b = f a then ENNReal.ofReal (μ a) else 0) =
      ENNReal.ofReal (if b = f a then μ a else 0) := by
    intro a
    split_ifs <;> simp only [ENNReal.ofReal_zero]
  simp only [toPMF_apply, he]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => by
    split_ifs
    · exact hμ a
    · exact le_rfl), push_apply]

theorem toPMF_map {α β : Type*} (μ : Mass α) (hμ : ∀ a, 0 ≤ μ a)
    (ht : total μ = 1) (f : α → β) :
    (toPMF μ hμ ht).map f =
      toPMF (μ.mapDomain f) (push_nonneg μ f hμ) (by rw [total_push, ht]) := by
  ext b
  rw [toPMF_map_apply, toPMF_apply]

theorem toPMF_bind_apply {α β : Type*} (ρ : Mass α) (hρ : ∀ a, 0 ≤ ρ a)
    (htρ : total ρ = 1) (μ : α → Mass β) (hμ : ∀ a b, 0 ≤ μ a b)
    (htμ : ∀ a, total (μ a) = 1) (b : β) :
    ((toPMF ρ hρ htρ).bind (fun a => toPMF (μ a) (hμ a) (htμ a))) b =
      ENNReal.ofReal (mixture ρ.support (fun a => ρ a) μ b) := by
  classical
  rw [PMF.bind_apply, tsum_eq_sum (s := ρ.support) (fun a ha => by
    rw [toPMF_apply, Finsupp.notMem_support_iff.mp ha]
    simp)]
  simp only [toPMF_apply, ← ENNReal.ofReal_mul (hρ _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg (hρ a) (hμ a b)), mixture_apply]

end Hindman168.FiniteMass
