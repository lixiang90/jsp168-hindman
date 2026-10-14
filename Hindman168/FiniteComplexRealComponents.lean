import Hindman168.FiniteComplexMassMean

namespace Hindman168.FiniteMass
open scoped BigOperators

theorem complexExpectation_re {α : Type*} (μ : Mass α) (f : α → ℂ) :
    (complexExpectation μ f).re = expectation μ (fun x => (f x).re) := by
  simp [complexExpectation, expectation, Finsupp.sum]

theorem complexExpectation_im {α : Type*} (μ : Mass α) (f : α → ℂ) :
    (complexExpectation μ f).im = expectation μ (fun x => (f x).im) := by
  simp [complexExpectation, expectation, Finsupp.sum]

/-- A real or imaginary component retains at least half of the discrepancy.
This is valid for arbitrary finite signed masses, including empty supports. -/
theorem complex_discrepancy_component {α : Type*} (μ ν : Mass α) (f : α → ℂ) :
    ‖complexExpectation μ f-complexExpectation ν f‖/2 ≤
        |expectation μ (fun x => (f x).re)-expectation ν (fun x => (f x).re)| ∨
      ‖complexExpectation μ f-complexExpectation ν f‖/2 ≤
        |expectation μ (fun x => (f x).im)-expectation ν (fun x => (f x).im)| := by
  have h := Complex.norm_le_abs_re_add_abs_im
    (complexExpectation μ f-complexExpectation ν f)
  simp only [Complex.sub_re, Complex.sub_im, complexExpectation_re,
    complexExpectation_im] at h
  by_cases hr : ‖complexExpectation μ f-complexExpectation ν f‖/2 ≤
      |expectation μ (fun x => (f x).re)-expectation ν (fun x => (f x).re)|
  · exact Or.inl hr
  · right
    have hrlt := lt_of_not_ge hr
    linarith

end Hindman168.FiniteMass

