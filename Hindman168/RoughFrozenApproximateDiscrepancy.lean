import Hindman168.RoughFrozenDiscrepancy

namespace Hindman168.FiniteMass

theorem rough_frozen_approximated_discrepancy {α : Type*} (μ ν : Mass α)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x)
    (htμ : total μ = 1) (htν : total ν = 1) (f frozen approx : α → ℝ)
    (η εfreeze εapprox : ℝ)
    (hfμ : ∀ x ∈ μ.support, |f x - frozen x| ≤ εfreeze)
    (hfν : ∀ x ∈ ν.support, |f x - frozen x| ≤ εfreeze)
    (haμ : ∀ x ∈ μ.support, |frozen x - approx x| ≤ εapprox)
    (haν : ∀ x ∈ ν.support, |frozen x - approx x| ≤ εapprox)
    (hbad : η ≤ |expectation μ f - expectation ν f|) :
    η - 2 * (εfreeze + εapprox) ≤ |expectation μ approx - expectation ν approx| := by
  apply rough_frozen_discrepancy μ ν hμ hν htμ htν f approx η (εfreeze + εapprox)
    _ _ hbad
  · intro x hx
    exact (abs_sub_le (f x) (frozen x) (approx x)).trans (add_le_add (hfμ x hx) (haμ x hx))
  · intro x hx
    exact (abs_sub_le (f x) (frozen x) (approx x)).trans (add_le_add (hfν x hx) (haν x hx))

end Hindman168.FiniteMass
