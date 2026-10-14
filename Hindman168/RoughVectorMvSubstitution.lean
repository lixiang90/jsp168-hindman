import Hindman168.RoughMvAffineSubstitution

/-! Genuine change of polynomial variables, preserving vector coefficients.
Linear variable expressions cannot increase the original total degree. -/
namespace Hindman168

noncomputable def roughVectorMvSubstitution {σ τ E : Type*}
    (f : σ → MvPolynomial τ ℝ) (p : RoughVectorMvPolynomial σ E) :
    RoughVectorMvPolynomial τ E :=
  p.map (fun a => (MvPolynomial.eval₂Hom MvPolynomial.C f a.1,a.2))

theorem rough_vector_mv_substitution_degree {σ τ E : Type*}
    (f : σ → MvPolynomial τ ℝ) (hf : ∀ j, (f j).totalDegree ≤ 1)
    {p : RoughVectorMvPolynomial σ E} {d : ℕ} (hp : RoughVectorMvDegreeLE p d) :
    RoughVectorMvDegreeLE (roughVectorMvSubstitution f p) d := by
  rintro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact (rough_mv_linear_substitution_degree f hf b.1).trans (hp b hb)

theorem rough_mv_substitution_eval {σ τ : Type*}
    (f : σ → MvPolynomial τ ℝ) (p : MvPolynomial σ ℝ) (x : τ → ℝ) :
    MvPolynomial.eval x (MvPolynomial.eval₂Hom MvPolynomial.C f p) =
      MvPolynomial.eval (fun j => MvPolynomial.eval x (f j)) p := by
  change MvPolynomial.eval x (MvPolynomial.eval₂ MvPolynomial.C f p) = _
  rw [←MvPolynomial.eval_assoc]
  rfl

theorem rough_vector_mv_substitution_eval {σ τ E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : σ → MvPolynomial τ ℝ) (p : RoughVectorMvPolynomial σ E) (x : τ → ℝ) :
    roughVectorMvEval (roughVectorMvSubstitution f p) x =
      roughVectorMvEval p (fun j => MvPolynomial.eval x (f j)) := by
  unfold roughVectorMvSubstitution roughVectorMvEval
  simp only [List.map_map,Function.comp_def,rough_mv_substitution_eval]

end Hindman168
