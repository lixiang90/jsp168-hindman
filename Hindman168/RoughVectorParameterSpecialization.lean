import Hindman168.RoughMvAffineSubstitution

namespace Hindman168
open MvPolynomial
variable {κ E : Type*}

noncomputable def roughMvParameterSpecialize (z : ℝ) :
    MvPolynomial (Option κ) ℝ →+* MvPolynomial κ ℝ :=
  eval₂Hom C (fun j => j.elim (C z) X)

theorem rough_mv_parameter_specialize_degree (z : ℝ) (p : MvPolynomial (Option κ) ℝ) :
    (roughMvParameterSpecialize z p).totalDegree ≤ p.totalDegree := by
  apply rough_mv_linear_substitution_degree
  intro j
  cases j with
  | none => simp only [Option.elim_none, totalDegree_C]; exact Nat.zero_le _
  | some j =>
      simpa only [Option.elim_some, X, Finsupp.sum_single_index, id_eq] using
        totalDegree_monomial_le (Finsupp.single j 1) (1 : ℝ)

theorem rough_mv_parameter_specialize_eval (z : ℝ) (p : MvPolynomial (Option κ) ℝ) (x : κ → ℝ) :
    eval x (roughMvParameterSpecialize z p) = eval (fun j => j.elim z x) p := by
  change eval x (eval₂ C _ p) = _
  rw [← eval_assoc]
  apply congrArg (fun v : Option κ → ℝ => eval v p)
  funext j
  cases j <;> simp only [Function.comp_apply, Option.elim_none, Option.elim_some, eval_C, eval_X]

noncomputable def roughVectorMvParameterSpecialize (z : ℝ)
    (p : RoughVectorMvPolynomial (Option κ) E) : RoughVectorMvPolynomial κ E :=
  p.map (fun a => (roughMvParameterSpecialize z a.1, a.2))

theorem rough_vector_parameter_specialize_degree (z : ℝ)
    {p : RoughVectorMvPolynomial (Option κ) E} {q : ℕ} (hp : RoughVectorMvDegreeLE p q) :
    RoughVectorMvDegreeLE (roughVectorMvParameterSpecialize z p) q := by
  rintro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact (rough_mv_parameter_specialize_degree z b.1).trans (hp b hb)

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rough_vector_parameter_specialize_eval (z : ℝ)
    (p : RoughVectorMvPolynomial (Option κ) E) (x : κ → ℝ) :
    roughVectorMvEval (roughVectorMvParameterSpecialize z p) x =
      roughVectorMvEval p (fun j => j.elim z x) := by
  simp only [roughVectorMvParameterSpecialize, roughVectorMvEval, List.map_map,
    Function.comp_def, rough_mv_parameter_specialize_eval]

end Hindman168
