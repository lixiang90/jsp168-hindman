import Hindman168.RoughMvAffineSubstitution

/-! Joint substitution leaves the progression parameter unchanged and
applies the original residue substitution to each spatial parameter. -/
namespace Hindman168
open MvPolynomial

noncomputable def roughSpatialSubstitution {κ R : Type*} [CommSemiring R]
    (u : κ → R) (K : R) : MvPolynomial (Option κ) R →+* MvPolynomial (Option κ) R :=
  roughMvAffineSubstitution (Option.elim · 0 u) (Option.elim · 1 (fun _ => K))

theorem roughSpatialSubstitution_degree {κ R : Type*} [CommSemiring R]
    (u : κ → R) (K : R) (p : MvPolynomial (Option κ) R) :
    (roughSpatialSubstitution u K p).totalDegree ≤ p.totalDegree :=
  roughMvAffineSubstitution_degree _ _ p

theorem roughSpatialSubstitution_eval {κ R : Type*} [CommSemiring R]
    (u x : κ → R) (K z : R) (p : MvPolynomial (Option κ) R) :
    eval (Option.elim · z x) (roughSpatialSubstitution u K p) =
      eval (Option.elim · z (fun j => u j + K * x j)) p := by
  rw [roughSpatialSubstitution, roughMvAffineSubstitution_eval]
  apply congrArg (fun v : Option κ → R => eval v p)
  funext j
  cases j <;> simp only [Option.elim_none, Option.elim_some, zero_add, one_mul]

end Hindman168
