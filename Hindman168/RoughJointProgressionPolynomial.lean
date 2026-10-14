import Hindman168.RoughMvAffineSubstitution

namespace Hindman168

theorem rough_joint_progression_polynomial {κ E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (log : G → E) (Q : (Option κ → ℝ) → G)
    (p : RoughVectorMvPolynomial (Option κ) E) (d : ℕ)
    (hd : RoughVectorMvDegreeLE p d)
    (hp : ∀ (z : ℝ) (y : κ → ℝ), roughVectorMvEval p (Option.elim · z y) =
      log (Q (Option.elim · z y))) (a b : ℝ) :
    ∃ pNew : RoughVectorMvPolynomial (Option κ) E,
      RoughVectorMvDegreeLE pNew d ∧
      ∀ (z : ℝ) (y : κ → ℝ), roughVectorMvEval pNew (Option.elim · z y) =
        log (Q (Option.elim · (a+b*z) y)) := by
  let u : Option κ → ℝ := (Option.elim · a (fun _ => 0))
  let k : Option κ → ℝ := (Option.elim · b (fun _ => 1))
  refine ⟨roughVectorMvAffineSubstitution u k p,
    roughVectorMvAffineSubstitution_degree u k hd, ?_⟩
  intro z y
  rw [roughVectorMvAffineSubstitution_eval]
  have he : (fun j => u j+k j*Option.elim j z y) = (Option.elim · (a+b*z) y) := by
    funext j
    cases j <;> simp only [u, k, Option.elim_none, Option.elim_some, zero_add, one_mul]
  rw [he, hp]

end Hindman168
