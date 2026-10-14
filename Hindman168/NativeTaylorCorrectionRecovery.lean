import Hindman168.NativeTaylorKernelAdaptation

/-! Recover the actual original polynomial from its collected correction
at EVERY real input. Smooth correction stays on the left and rational
integer correction stays on the right, in the paper's exact order. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_taylor_correction_factor_recovery {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (j : ℕ) (epsilon : ℝ) (m : ℤ) (V : D.E) (b : ℝ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p (fun _ => b)) =
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        ((epsilon * MvPolynomial.eval (fun _ => b) (adaptedTaylorBinomial j)) • V) *
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) (roughVectorMvCollect
          (nativeTaylorDescentCorrection D p j epsilon m V)) (fun _ => b)) *
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (((m : ℝ) * MvPolynomial.eval (fun _ => b) (adaptedTaylorBinomial j)) • V) := by
  let exp : D.E → D.G := nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
  let B := MvPolynomial.eval (fun _ => b) (adaptedTaylorBinomial j)
  let left := exp ((epsilon * B) • V)
  let right := exp (((m : ℝ) * B) • V)
  have hneg (r : ℝ) : exp ((-r * B) • V) = (exp ((r*B) • V))⁻¹ :=
    (congrArg exp (by rw [neg_mul, neg_smul]; rfl)).trans
      (nativeLieExponential_neg (E := D.E) (I := D.I) (G := D.G) ((r*B) • V))
  have he := native_taylor_descent_correction_exponential D p j epsilon m V b
  have hg := congrArg₂ (fun a c : D.G => a * exp (roughVectorMvEval (E := D.E) p (fun _ => b)) * c)
    (hneg epsilon) (hneg (m : ℝ))
  have hq : exp (roughVectorMvEval (E := D.E) (roughVectorMvCollect
      (nativeTaylorDescentCorrection D p j epsilon m V)) (fun _ => b)) =
    left⁻¹ * exp (roughVectorMvEval (E := D.E) p (fun _ => b)) * right⁻¹ :=
    (congrArg exp (rough_vector_collect_eval _ _)).trans (he.trans hg)
  calc
    exp (roughVectorMvEval (E := D.E) p (fun _ => b)) =
        left * (left⁻¹ * exp (roughVectorMvEval (E := D.E) p (fun _ => b)) * right⁻¹) * right := by group
    _ = left * exp (roughVectorMvEval (E := D.E) (roughVectorMvCollect
        (nativeTaylorDescentCorrection D p j epsilon m V)) (fun _ => b)) * right :=
      congrArg (fun g : D.G => left * g * right) hq.symm

end Hindman168
