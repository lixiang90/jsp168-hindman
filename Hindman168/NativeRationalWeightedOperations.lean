import Hindman168.NativeRationalLieFiltration
import Hindman168.NativeRationalFilteredIdeals
import Hindman168.RoughParametricWeightedPicard
import Hindman168.NativeConstantProductPerturbation
import Hindman168.NativeArbitraryLieFilteredPolynomial

/-! Actual native product/perturbation weights for any original rational
Lie filtration, with actual original group/Exp compatibility supplied. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_product_polynomial_weighted {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {p q : RoughVectorMvPolynomial σ D.E} {k : ℕ}
    (hp : RoughVectorMvWeightedDegree F.layer p k) (hq : RoughVectorMvWeightedDegree F.layer q k) :
    RoughVectorMvWeightedDegree F.layer (roughNativeProductMvPolynomial (I := D.I) (G := D.G) p q) k := by
  apply rough_parametric_weighted_endpoint
  exact rough_parametric_weighted_picard F.layer F.antitone _ F.bracket _ hq hp _

theorem native_rational_product_perturbation_weighted {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {u0 u1 du w0 w1 dw : RoughVectorMvPolynomial σ D.E} {k l : ℕ}
    (hu0 : RoughVectorMvWeightedDegree F.layer u0 k) (hu1 : RoughVectorMvWeightedDegree F.layer u1 k)
    (hw0 : RoughVectorMvWeightedDegree F.layer w0 k) (hw1 : RoughVectorMvWeightedDegree F.layer w1 k)
    (hdu : RoughVectorMvWeightedDegree F.layer du l) (hdw : RoughVectorMvWeightedDegree F.layer dw l) :
    RoughVectorMvWeightedDegree F.layer (nativeProductPerturbationPolynomial D u0 u1 du w0 w1 dw) l := by
  apply rough_parametric_weighted_endpoint
  exact rough_parametric_picard_perturbation_weighted F.layer F.antitone _ F.bracket _ hw0 hw1 hu0 hu1 hdw hdu _

theorem native_rational_constant_zero_weighted {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (v : D.E) :
    RoughVectorMvWeightedDegree F.layer (roughVectorMvConstant (σ := σ) v) 0 := by
  apply rough_vector_constant_weighted
  rw [F.zero]; exact Submodule.mem_top

theorem native_rational_constant_product_perturbation_weighted {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (v : D.E) :
    RoughVectorMvWeightedDegree F.layer (nativeRightConstantPerturbation D p v) 1 ∧
      RoughVectorMvWeightedDegree F.layer (nativeLeftConstantPerturbation D p v) 1 := by
  have hc1 : RoughVectorMvWeightedDegree F.layer (roughVectorMvConstant (σ := σ) v) 1 := by
    apply rough_vector_constant_weighted
    rw [F.one]; exact Submodule.mem_top
  have hc0 := native_rational_constant_zero_weighted (σ := σ) D F v
  have he0 : RoughVectorMvWeightedDegree F.layer ([] : RoughVectorMvPolynomial σ D.E) 0 :=
    fun a ha => False.elim (List.not_mem_nil ha)
  have he1 : RoughVectorMvWeightedDegree F.layer ([] : RoughVectorMvPolynomial σ D.E) 1 :=
    fun a ha => False.elim (List.not_mem_nil ha)
  exact ⟨native_rational_product_perturbation_weighted D F hp hp he0 hc0 he1 hc1,
    native_rational_product_perturbation_weighted D F he0 hc0 hp hp hc1 he1⟩

theorem native_rational_weighted_real_polynomial_filtered {s ℓ : ℕ} {σ : Type*} [Fintype σ]
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {p : RoughVectorMvPolynomial σ D.E} (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    RoughFilteredPolynomial (nativeRationalFilteredGroupLayer D F)
      (fun x : σ → ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p x)) :=
  native_arbitrary_lie_polynomial_filtered D F.layer F.antitone F.bracket
    (nativeRationalFilteredGroupLayer D F) (fun _ v hv => ⟨v,hv,rfl⟩) p hp

end Hindman168
