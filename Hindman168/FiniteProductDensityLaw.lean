import Hindman168.FiniteProductExpectations

/-! Exact product density conversion for finite signed masses.
The comparison masses retain all their original coefficients. -/

namespace Hindman168.FiniteMass
open scoped BigOperators Classical

theorem expectation_piMass_density {ι α : Type*} [Fintype ι]
    (μ ν : ι → Mass α) (ρ : ι → α → ℝ)
    (hν : ∀ i y, ν i y = μ i y * ρ i y) (f : (ι → α) → ℝ) :
    expectation (piMass ν) f =
      expectation (piMass μ) (fun z => (∏ i, ρ i (z i)) * f z) := by
  have hp (z : ι → α) : piMass ν z = piMass μ z * ∏ i, ρ i (z i) := by
    simp only [piMass_apply, hν, Finset.prod_mul_distrib]
  have hs : (piMass ν).support ⊆ (piMass μ).support := by
    intro z hz
    apply Finsupp.mem_support_iff.mpr
    intro he
    apply Finsupp.mem_support_iff.mp hz
    rw [hp, he, zero_mul]
  rw [expectation_eq_sum _ _ hs]
  simp only [expectation, Finsupp.sum, hp, mul_assoc]

end Hindman168.FiniteMass
