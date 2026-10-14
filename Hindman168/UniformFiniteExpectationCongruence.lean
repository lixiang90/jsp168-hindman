import Hindman168.UniformFiniteMass

namespace Hindman168.FiniteMass
open scoped BigOperators Classical

theorem uniformFinsetMass_expectation_congr {α : Type*} (S : Finset α) (f g : α → ℝ)
    (hfg : ∀ x ∈ S, f x = g x) :
    expectation (uniformFinsetMass S) f = expectation (uniformFinsetMass S) g := by
  unfold expectation Finsupp.sum
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only
  rw [hfg x (flatMass_support S _ hx)]

end Hindman168.FiniteMass
