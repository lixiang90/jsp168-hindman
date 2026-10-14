import Hindman168.NativeRationalFractionalCommutator

/-! Actual real fractional bracket expression and exact finite-density
transport. No quantitative bracket inverse is taken as a premise. -/
namespace Hindman168
open scoped BigOperators

noncomputable def scalarFractionalBracket {ι : Type*} [Fintype ι]
    (β α : ℝ) (ζ γ : ι → ℝ) (h : ℝ) : ℝ :=
  β+α*h+∑ i, ζ i*Int.fract (h*γ i)

theorem finite_refinement_density (ρ n c u v : ℝ) (hc : 0 < c)
    (hu : ρ*n ≤ u) (hv : u ≤ c*v) : (ρ/c)*n ≤ v := by
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hc).mpr (by nlinarith [hu.trans hv])

end Hindman168
