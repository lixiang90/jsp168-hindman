import Hindman168.RoughVectorWeightedDegree
import Hindman168.RoughVectorMvCoefficients
import Mathlib.Algebra.MvPolynomial.Rename

/-! TRUE variable renaming of actual vector coefficient polynomials retains
evaluations and complete scalar polynomials and transports genuine weights. -/

namespace Hindman168
variable {σ τ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roughVectorMvRename (f : σ → τ) (p : RoughVectorMvPolynomial σ E) :
    RoughVectorMvPolynomial τ E := p.map (fun a => (MvPolynomial.rename f a.1,a.2))

theorem rough_vector_rename_eval (f : σ → τ) (p : RoughVectorMvPolynomial σ E) (x : τ → ℝ) :
    roughVectorMvEval (roughVectorMvRename f p) x = roughVectorMvEval p (x ∘ f) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      change MvPolynomial.eval x (MvPolynomial.rename f a.1) • a.2 +
        roughVectorMvEval (roughVectorMvRename f p) x =
        MvPolynomial.eval (x ∘ f) a.1 • a.2 + roughVectorMvEval p (x ∘ f)
      rw [MvPolynomial.eval_rename,ih]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem rough_vector_rename_degree (f : σ → τ) {p : RoughVectorMvPolynomial σ E} {d : ℕ}
    (hp : RoughVectorMvDegreeLE p d) : RoughVectorMvDegreeLE (roughVectorMvRename f p) d := by
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact (MvPolynomial.totalDegree_rename_le f b.1).trans (hp b hb)

theorem rough_vector_rename_weighted (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    (f : σ → τ) {p : RoughVectorMvPolynomial σ E} {k : ℕ} (hp : RoughVectorMvWeightedDegree F p k) :
    RoughVectorMvWeightedDegree F (roughVectorMvRename f p) k := by
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact hF (Nat.add_le_add_right (MvPolynomial.totalDegree_rename_le f b.1) k) (hp b hb)

theorem rough_vector_rename_projection (f : σ → τ) (ell : E →ₗ[ℝ] ℝ) (p : RoughVectorMvPolynomial σ E) :
    roughVectorMvProjection ell (roughVectorMvRename f p) = MvPolynomial.rename f (roughVectorMvProjection ell p) := by
  induction p with
  | nil => exact (map_zero _).symm
  | cons a p ih =>
      change MvPolynomial.rename f a.1 * MvPolynomial.C (ell a.2) +
        roughVectorMvProjection ell (roughVectorMvRename f p) =
        MvPolynomial.rename f (a.1 * MvPolynomial.C (ell a.2) + roughVectorMvProjection ell p)
      rw [map_add,map_mul,MvPolynomial.rename_C,ih]

end Hindman168
