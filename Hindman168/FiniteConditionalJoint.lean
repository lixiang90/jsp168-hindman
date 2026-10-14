import Hindman168.FiniteWeightedCauchySchwarz

/-!
# The original finite joint law for conditional outside parameters

A dependent inner mass is joined to its original outside mass by a finite
mixture. Fubini is exact for signed tests. In particular an inner sampling
law may depend on the primes without introducing an independence premise.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem expectation_mass_add {α : Type*} (μ ν : Mass α) (f : α → ℝ) :
    expectation (μ + ν) f = expectation μ f + expectation ν f :=
  Finsupp.sum_add_index' (by intros; simp) (by intros; simp [add_mul])

theorem expectation_mass_smul {α : Type*} (c : ℝ) (μ : Mass α) (f : α → ℝ) :
    expectation (c • μ) f = c * expectation μ f := by
  unfold expectation
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
  simp only [Finsupp.sum, Finset.mul_sum, mul_assoc]

theorem expectation_mixture {α ι : Type*} (S : Finset ι) (p : ι → ℝ)
    (μ : ι → Mass α) (f : α → ℝ) :
    expectation (mixture S p μ) f = ∑ i ∈ S, p i * expectation (μ i) f := by
  unfold mixture
  induction S using Finset.induction_on with
  | empty => simp [expectation]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, expectation_mass_add, expectation_mass_smul,
      ih, Finset.sum_insert hi]

noncomputable def conditionalJoint {α β : Type*} (μ : Mass α) (ν : α → Mass β) :
    Mass (α × β) :=
  mixture μ.support (fun x => μ x) (fun x => (ν x).mapDomain (fun y => (x, y)))

theorem expectation_conditionalJoint {α β : Type*} (μ : Mass α) (ν : α → Mass β)
    (f : α × β → ℝ) :
    expectation (conditionalJoint μ ν) f =
      expectation μ (fun x => expectation (ν x) (fun y => f (x, y))) := by
  rw [conditionalJoint, expectation_mixture]
  simp only [expectation_push]
  rfl

theorem conditionalJoint_nonneg {α β : Type*} (μ : Mass α) (ν : α → Mass β)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x ∈ μ.support, ∀ y, 0 ≤ ν x y) (p : α × β) :
    0 ≤ conditionalJoint μ ν p :=
  mixture_nonneg (fun x _ => hμ x)
    (fun x hx => push_nonneg (ν x) (fun y => (x, y)) (hν x hx)) p

theorem conditionalJoint_total {α β : Type*} (μ : Mass α) (ν : α → Mass β) :
    total (conditionalJoint μ ν) = expectation μ (fun x => total (ν x)) := by
  rw [conditionalJoint, mixture_total]
  simp only [total_push]
  rfl

end Hindman168.FiniteMass
