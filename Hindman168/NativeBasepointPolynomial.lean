import Hindman168.RoughGroupBasepointNormalization
import Hindman168.RoughNativeProductWeighted
import Hindman168.RoughVectorMvConstant
import Hindman168.NativeNilmanifoldData
import Hindman168.RoughNativeWeightedPolynomial

/-! An ACTUAL logarithmic coefficient polynomial for original basepoint
normalization, with SAME original Lie-filtration weights. Constants may
be unbounded; no spatial regularity or ordinary-degree preservation is assumed. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeBasepointRawPolynomial {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (r : D.G) :
    RoughVectorMvPolynomial σ D.E :=
  roughNativeProductMvPolynomial (I := D.I) (G := D.G)
    (roughVectorMvConstant (-nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) r))
    (roughNativeProductMvPolynomial (I := D.I) (G := D.G) p
      (roughNativeProductMvPolynomial (I := D.I) (G := D.G)
        (roughVectorMvConstant (-roughVectorMvEval (E := D.E) p (fun _ => 0)))
        (roughVectorMvConstant (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) r))))

theorem native_basepoint_raw_polynomial_eval {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (r : D.G) (x : σ → ℝ) :
    roughVectorMvEval (E := D.E) (nativeBasepointRawPolynomial D p r) x =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (roughGroupBasepointNormalization
          (fun y : σ → ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) p y)) r x) := by
  have hn : ∀ v : D.E, nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (-v) =
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v)⁻¹ := by
    intro v
    exact nativeLieExponential_neg (E := D.E) (I := D.I) (G := D.G) v
  simp only [nativeBasepointRawPolynomial,roughNativeProductMvPolynomial_eval,
    rough_vector_constant_eval,nativeLieExponential_globalLogarithm,hn]
  simp only [roughGroupBasepointNormalization,mul_assoc]
  have hzero : (fun _ : σ => (0 : ℝ)) = (0 : σ → ℝ) := by
    funext i
    rfl
  rw [hzero]

theorem native_basepoint_raw_polynomial_weighted {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvDegreeLE p d) (r : D.G) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d)
      (nativeBasepointRawPolynomial D p r) 0 := by
  have hc : ∀ v : D.E, RoughVectorMvWeightedDegree
      (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d)
      (roughVectorMvConstant (σ := σ) v) 0 := by
    intro v
    apply rough_vector_constant_weighted
    rw [rough_native_stretched_lie_initial d hd 0 (Nat.zero_le d)]
    exact Submodule.mem_top
  unfold nativeBasepointRawPolynomial
  apply rough_native_product_polynomial_weighted d hd (hc _)
  apply rough_native_product_polynomial_weighted d hd
    (rough_native_weighted_polynomial_initial d hd hp)
  exact rough_native_product_polynomial_weighted d hd (hc _) (hc _)

end Hindman168
