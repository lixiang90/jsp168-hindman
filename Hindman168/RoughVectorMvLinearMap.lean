import Hindman168.RoughVectorMvPolynomial

namespace Hindman168

noncomputable def roughVectorMvLinearMap {σ E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (L : E →ₗ[ℝ] F) (p : RoughVectorMvPolynomial σ E) :
    RoughVectorMvPolynomial σ F := p.map (fun a => (a.1, L a.2))

theorem roughVectorMvLinearMap_degree {σ E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (L : E →ₗ[ℝ] F) {p : RoughVectorMvPolynomial σ E}
    {d : ℕ} (hp : RoughVectorMvDegreeLE p d) :
    RoughVectorMvDegreeLE (roughVectorMvLinearMap L p) d := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact hp b hb

theorem roughVectorMvLinearMap_eval {σ E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →ₗ[ℝ] F) (p : RoughVectorMvPolynomial σ E) (x : σ → ℝ) :
    roughVectorMvEval (roughVectorMvLinearMap L p) x = L (roughVectorMvEval p x) := by
  induction p with
  | nil => simp [roughVectorMvLinearMap, roughVectorMvEval]
  | cons a p ih =>
    change MvPolynomial.eval x a.1 • L a.2 + roughVectorMvEval (roughVectorMvLinearMap L p) x =
      L (MvPolynomial.eval x a.1 • a.2 + roughVectorMvEval p x)
    rw [ih, map_add, map_smul]

end Hindman168
