import Hindman168.NativeNilmanifoldData
import Hindman168.RoughNativeProductMvPolynomial
import Hindman168.RoughParametricPicardPerturbation
import Hindman168.RoughNativeStretchedLieBracket

/-! ACTUAL original native logarithmic product perturbation polynomial.
Original input differences give EXACT product-log differences, with genuine
original Lie-filtration weights of the perturbations retained. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeProductPerturbationPolynomial {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s)
    (u0 u1 du w0 w1 dw : RoughVectorMvPolynomial σ D.E) : RoughVectorMvPolynomial σ D.E :=
  roughParametricEndpoint (roughParametricPicardPerturbation
    (nativeLieAdjointDifferential (I := D.I) (G := D.G)) (Group.nilpotencyClass D.G)
      w0 w1 dw u0 u1 du (Group.nilpotencyClass D.G+1))

theorem native_product_perturbation_polynomial_eval {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s)
    (u0 u1 du w0 w1 dw : RoughVectorMvPolynomial σ D.E)
    (hu : ∀ x, roughVectorMvEval (E := D.E) du x = roughVectorMvEval (E := D.E) u1 x-roughVectorMvEval (E := D.E) u0 x)
    (hw : ∀ x, roughVectorMvEval (E := D.E) dw x = roughVectorMvEval (E := D.E) w1 x-roughVectorMvEval (E := D.E) w0 x)
    (x : σ → ℝ) :
    roughVectorMvEval (E := D.E) (nativeProductPerturbationPolynomial D u0 u1 du w0 w1 dw) x =
      roughVectorMvEval (E := D.E) (roughNativeProductMvPolynomial (I := D.I) (G := D.G) u1 w1) x-
      roughVectorMvEval (E := D.E) (roughNativeProductMvPolynomial (I := D.I) (G := D.G) u0 w0) x := by
  have he := rough_parametric_picard_perturbation_eval
    (nativeLieAdjointDifferential (I := D.I) (G := D.G)) (Group.nilpotencyClass D.G)
    w0 w1 dw u0 u1 du hw hu (Group.nilpotencyClass D.G+1) x 1
  simp only [← rough_parametric_eval_endpoint] at he
  exact he

theorem native_product_perturbation_polynomial_weighted {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    {u0 u1 du w0 w1 dw : RoughVectorMvPolynomial σ D.E} {k l : ℕ}
    (hu0 : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d) u0 k)
    (hu1 : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d) u1 k)
    (hw0 : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d) w0 k)
    (hw1 : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d) w1 k)
    (hdu : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d) du l)
    (hdw : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d) dw l) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d)
      (nativeProductPerturbationPolynomial D u0 u1 du w0 w1 dw) l := by
  apply rough_parametric_weighted_endpoint
  exact rough_parametric_picard_perturbation_weighted _ (rough_native_stretched_lie_antitone d hd) _
    (fun _ _ _ _ h1 h2 => rough_native_stretched_lie_bracket d hd h1 h2) _ hw0 hw1 hu0 hu1 hdw hdu _

end Hindman168
