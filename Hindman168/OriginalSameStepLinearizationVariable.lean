import OAI.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution

/-! Exact transport from a `Unit` polynomial variable to `Fin 1`, preserving
all integer evaluations. No orbit coefficient or observable is changed. -/

namespace Hindman168.OriginalSameStepLinearization

open OAI.Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

noncomputable def oneVariableOrbit (F : NilpotentLieFiltration L s) :
    F.PolynomialOrbit (fun _ : Unit => 1) →*
      F.PolynomialOrbit (fun _ : Fin 1 => 1) :=
  F.polynomialOrbitSubstitute (fun _ => MvPolynomial.X (0 : Fin 1))
    (fun _ => weightedSupportLE_X (fun _ => 1) 0)

@[simp] theorem oneVariableOrbit_eval (F : NilpotentLieFiltration L s)
    (p : F.PolynomialOrbit (fun _ : Unit => 1)) (n : ℤ) :
    F.polynomialOrbitEval (fun _ => 1) (fun _ : Fin 1 => n) (oneVariableOrbit F p) =
      F.polynomialOrbitEval (fun _ => 1) (fun _ : Unit => n) p :=
  F.polynomialOrbitSubstitute_eval (fun _ => MvPolynomial.X (0 : Fin 1))
    (fun _ => weightedSupportLE_X (fun _ => 1) 0) p (fun _ => n) (fun _ => n)
    (fun _ => MvPolynomial.aeval_X _ _)

end Hindman168.OriginalSameStepLinearization
