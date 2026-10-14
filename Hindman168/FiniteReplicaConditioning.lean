import Hindman168.FiniteReplicaJointLaw
import Hindman168.ConditionalRoughCoprimality
import Hindman168.FiniteEventPairLaw

/-!
# Exact separate good-event conditioning of independent replicas

Conditioning each original replica preserves independence and divides by
exactly the product of its actual event masses. All finite identities also
hold when a denominator is zero; probability and asymptotic applications
will establish positive masses from the good-event limits.
-/

namespace Hindman168.FiniteMass

open Filter
open scoped BigOperators Topology Classical

theorem expectation_conditionMass {α : Type*} (μ : Mass α) (E : α → Prop) (f : α → ℝ) :
    expectation (conditionMass μ E) f =
      expectation μ (fun x => if E x then f x else 0) / event μ E := by
  change expectation ((event μ E)⁻¹ • restrictedMass μ E) f = _
  rw [expectation_mass_smul, expectation_restrictedMass]
  simp only [div_eq_mul_inv, mul_comm]

theorem piMass_conditionMass {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ∀ i, Mass (α i)) (E : ∀ i, α i → Prop) :
    piMass (fun i => conditionMass (μ i) (E i)) =
      (∏ i, event (μ i) (E i))⁻¹ • restrictedMass (piMass μ) (fun x => ∀ i, E i (x i)) := by
  ext x
  simp only [piMass_apply, conditionMass_apply, Finsupp.smul_apply, smul_eq_mul, restrictedMass_apply]
  by_cases hx : ∀ i, E i (x i)
  · simp only [if_pos hx]
    simp_rw [if_pos (hx _)]
    rw [Finset.prod_div_distrib]
    simp only [div_eq_mul_inv, mul_comm]
  · rw [if_neg hx, mul_zero]
    obtain ⟨i, hi⟩ := not_forall.mp hx
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact if_neg hi

theorem expectation_piMass_conditionMass {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ∀ i, Mass (α i)) (E : ∀ i, α i → Prop) (f : (∀ i, α i) → ℝ) :
    expectation (piMass (fun i => conditionMass (μ i) (E i))) f =
      expectation (piMass μ) (fun x => if ∀ i, E i (x i) then f x else 0) /
        ∏ i, event (μ i) (E i) := by
  rw [piMass_conditionMass, expectation_mass_smul, expectation_restrictedMass]
  simp only [div_eq_mul_inv, mul_comm]
  congr 1
  apply congrArg (expectation (piMass μ))
  funext x
  split_ifs <;> rfl

theorem event_piMass_all {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ∀ i, Mass (α i)) (E : ∀ i, α i → Prop) :
    event (piMass μ) (fun x => ∀ i, E i (x i)) = ∏ i, event (μ i) (E i) := by
  have hind (x : ∀ i, α i) : (if ∀ i, E i (x i) then (1 : ℝ) else 0) =
      ∏ i, if E i (x i) then (1 : ℝ) else 0 := by
    by_cases hx : ∀ i, E i (x i)
    · simp only [if_pos hx]
      simp_rw [if_pos (hx _)]
      simp
    · rw [if_neg hx]
      obtain ⟨i, hi⟩ := not_forall.mp hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm
  rw [← expectation_indicator]
  have hh := expectation_piMass_product μ (fun i x => if E i x then (1 : ℝ) else 0)
  calc
    _ = expectation (piMass μ) (fun x => ∏ i, if E i (x i) then 1 else 0) := by
      apply congrArg (expectation (piMass μ))
      funext x
      by_cases hx : ∀ i, E i (x i)
      · simpa only [if_pos hx] using hind x
      · simpa only [if_neg hx] using hind x
    _ = ∏ i, event (μ i) (E i) := hh.trans
      (Finset.prod_congr rfl (fun i _ => expectation_indicator (μ i) (E i)))

theorem conditioned_replicas_zero_limit {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ℕ → ∀ i, Mass (α i)) (E : ℕ → ∀ i, α i → Prop)
    (f : ℕ → (∀ i, α i) → ℝ)
    (hE : ∀ i, Tendsto (fun w => event (μ w i) (E w i)) atTop (𝓝 1))
    (hf : Tendsto (fun w => expectation (piMass (μ w))
      (fun x => if ∀ i, E w i (x i) then f w x else 0)) atTop (𝓝 0)) :
    Tendsto (fun w => expectation (piMass (fun i => conditionMass (μ w i) (E w i))) (f w))
      atTop (𝓝 0) := by
  have hp : Tendsto (fun w => ∏ i, event (μ w i) (E w i)) atTop (𝓝 1) := by
    simpa only [Finset.prod_const_one] using tendsto_finsetProd Finset.univ (fun i _ => hE i)
  have hz := hf.div hp (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun w : ℕ => (expectation (piMass (μ w))
    (fun x => if ∀ i, E w i (x i) then f w x else 0)) / ∏ i, event (μ w i) (E w i))
    atTop (𝓝 ((0 : ℝ) / 1)) at hz
  have hfun : (fun w => expectation (piMass (fun i => conditionMass (μ w i) (E w i))) (f w)) =
      (fun w => expectation (piMass (μ w))
        (fun x => if ∀ i, E w i (x i) then f w x else 0) / ∏ i, event (μ w i) (E w i)) := by
    funext w
    exact expectation_piMass_conditionMass (μ w) (E w) (f w)
  rw [hfun]
  simpa only [zero_div] using hz

end Hindman168.FiniteMass
