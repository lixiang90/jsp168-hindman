import Hindman168.FiniteWeightedErrors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Hindman168.FiniteMass

theorem rough_frozen_discrepancy {α : Type*} (μ ν : Mass α)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x)
    (htμ : total μ = 1) (htν : total ν = 1) (f g : α → ℝ) (η ε : ℝ)
    (hfμ : ∀ x ∈ μ.support, |f x - g x| ≤ ε)
    (hfν : ∀ x ∈ ν.support, |f x - g x| ≤ ε)
    (hbad : η ≤ |expectation μ f - expectation ν f|) :
    η - 2 * ε ≤ |expectation μ g - expectation ν g| := by
  have h1 : |expectation μ f - expectation μ g| ≤ ε := by
    simpa only [htμ, one_mul] using expectation_difference_support_bound μ hμ f g ε hfμ
  have h2 : |expectation ν g - expectation ν f| ≤ ε := by
    rw [abs_sub_comm]
    simpa only [htν, one_mul] using expectation_difference_support_bound ν hν f g ε hfν
  have hb : |expectation μ f - expectation ν f| ≤
      ε + |expectation μ g - expectation ν g| + ε := by
    calc
      _ = |(expectation μ f - expectation μ g) + (expectation μ g - expectation ν g) +
          (expectation ν g - expectation ν f)| := by congr 1; ring
      _ ≤ |expectation μ f - expectation μ g| + |expectation μ g - expectation ν g| +
          |expectation ν g - expectation ν f| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add h1 le_rfl) h2
  linarith

end Hindman168.FiniteMass
