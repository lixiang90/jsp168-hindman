import Hindman168.OriginalSameStepLinearizationModelOrbit
import Hindman168.OriginalSameStepLinearizationVariable

/-! Exact transport from the upstream `Unit` variable to the singleton finite
variable of the fixed shift construction. This does not alter observables. -/

namespace Hindman168.OriginalSameStepLinearization

open OAI.Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable [FiniteDimensional ℚ L] {d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (hs : 1 ≤ s)

/-- The exact algebraic and quotient part of same-step linearization, now in
    precisely the one-variable interface of the upstream inverse theorem. -/
theorem exists_linear_orbit_for_polynomial
    (p : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)) :
    ∃ (g x : (ambientModel D hs).RealGroup)
      (u : ℤ → (fiberModel D hs).RealGroup),
      (∀ n, realFiberEvaluation D.filtration 1 0 (u n) =
        D.filtration.realification.polynomialOrbitEval (fun _ => 1) (fun _ : Unit => n) p) ∧
      ∀ n, (QuotientGroup.mk (g ^ n * x) : (ambientModel D hs).Space) =
        QuotientGroup.mk (modelFiberInclusion D hs (u n)) := by
  obtain ⟨q, hq⟩ := exists_realAdaptedEvaluation_lift D.filtration
    (oneVariableOrbit D.filtration.realification p)
  obtain ⟨g, x, u, hu, horbit⟩ := exists_linear_orbit_fiber D hs q
  refine ⟨g, x, u, fun n => ?_, horbit⟩
  rw [hu, hq, oneVariableOrbit_eval]

end Hindman168.OriginalSameStepLinearization
