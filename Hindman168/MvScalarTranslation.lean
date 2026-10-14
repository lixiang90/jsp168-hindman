import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Analysis.Complex.Basic

namespace Hindman168

noncomputable def mvScalarTranslation {σ : Type*} (q : MvPolynomial σ ℝ) (h : σ → ℝ) :
    MvPolynomial σ ℝ := MvPolynomial.bind₁ (fun i => MvPolynomial.X i+MvPolynomial.C (h i)) q

theorem mv_scalar_translation_eval {σ : Type*} (q : MvPolynomial σ ℝ) (h x : σ → ℝ) :
    MvPolynomial.eval x (mvScalarTranslation q h) = MvPolynomial.eval (fun i => x i+h i) q := by
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) x (MvPolynomial.bind₁ _ q) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  simp only [map_add,MvPolynomial.eval₂Hom_X',MvPolynomial.eval₂Hom_C,RingHom.id_apply]
  rfl

end Hindman168
