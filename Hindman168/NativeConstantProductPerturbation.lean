import Hindman168.NativeProductPerturbationPolynomial
import Hindman168.RoughVectorMvConstant

/-! ACTUAL original constant left/right product corrections have weight
ONE in SAME original stretched Lie filtration. Constants may be unbounded;
their membership in actual original layer ONE is proved from positive stretch. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRightConstantPerturbation {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (v : D.E) :
    RoughVectorMvPolynomial σ D.E :=
  nativeProductPerturbationPolynomial D p p [] [] (roughVectorMvConstant v) (roughVectorMvConstant v)

noncomputable def nativeLeftConstantPerturbation {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (v : D.E) :
    RoughVectorMvPolynomial σ D.E :=
  nativeProductPerturbationPolynomial D [] (roughVectorMvConstant v) (roughVectorMvConstant v) p p []

theorem native_right_constant_perturbation_eval {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (v : D.E) (x : σ → ℝ) :
    roughVectorMvEval (E := D.E) (nativeRightConstantPerturbation D p v) x =
      roughVectorMvEval (E := D.E) (roughNativeProductMvPolynomial (I := D.I) (G := D.G) p (roughVectorMvConstant v)) x-
        roughVectorMvEval (E := D.E) p x := by
  have he := native_product_perturbation_polynomial_eval D p p [] [] (roughVectorMvConstant v)
    (roughVectorMvConstant v) (fun y => by simp only [roughVectorMvEval,List.map_nil,List.sum_nil,sub_self])
    (fun y => by simp only [roughVectorMvEval,List.map_nil,List.sum_nil,sub_zero]) x
  have hb : roughVectorMvEval (E := D.E) (roughNativeProductMvPolynomial (I := D.I) (G := D.G) p []) x =
      roughVectorMvEval (E := D.E) p x := by
    have ht := roughNativeProductMvPolynomial_eval (E := D.E) (I := D.I) (G := D.G) p [] x
    have hz : roughVectorMvEval (E := D.E) ([] : RoughVectorMvPolynomial σ D.E) x = 0 := rfl
    have he0 : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) ([] : RoughVectorMvPolynomial σ D.E) x) = 1 := by
      exact (congrArg (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)) hz).trans
        (nativeLieExponential_zero (E := D.E) (I := D.I) (G := D.G))
    have hm := congrArg (fun z : D.G => nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p x) * z)) he0
    exact ht.trans (hm.trans ((congrArg (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G))
      (mul_one _)).trans (nativeLieGlobalLogarithm_exponential (E := D.E) (I := D.I) (G := D.G) _)))
  rw [hb] at he
  exact he

theorem native_left_constant_perturbation_eval {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (v : D.E) (x : σ → ℝ) :
    roughVectorMvEval (E := D.E) (nativeLeftConstantPerturbation D p v) x =
      roughVectorMvEval (E := D.E) (roughNativeProductMvPolynomial (I := D.I) (G := D.G) (roughVectorMvConstant v) p) x-
        roughVectorMvEval (E := D.E) p x := by
  have he := native_product_perturbation_polynomial_eval D [] (roughVectorMvConstant v) (roughVectorMvConstant v)
    p p [] (fun y => by simp only [roughVectorMvEval,List.map_nil,List.sum_nil,sub_zero])
    (fun y => by simp only [roughVectorMvEval,List.map_nil,List.sum_nil,sub_self]) x
  have hb : roughVectorMvEval (E := D.E) (roughNativeProductMvPolynomial (I := D.I) (G := D.G) [] p) x =
      roughVectorMvEval (E := D.E) p x := by
    have ht := roughNativeProductMvPolynomial_eval (E := D.E) (I := D.I) (G := D.G) [] p x
    have hz : roughVectorMvEval (E := D.E) ([] : RoughVectorMvPolynomial σ D.E) x = 0 := rfl
    have he0 : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) ([] : RoughVectorMvPolynomial σ D.E) x) = 1 := by
      exact (congrArg (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)) hz).trans
        (nativeLieExponential_zero (E := D.E) (I := D.I) (G := D.G))
    have hm := congrArg (fun z : D.G => nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (z * nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p x))) he0
    exact ht.trans (hm.trans ((congrArg (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G))
      (one_mul _)).trans (nativeLieGlobalLogarithm_exponential (E := D.E) (I := D.I) (G := D.G) _)))
  rw [hb] at he
  exact he

theorem native_constant_product_perturbation_weighted {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial σ D.E)
    (hp : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d) p 0)
    (v : D.E) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d)
      (nativeRightConstantPerturbation D p v) 1 ∧
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d)
      (nativeLeftConstantPerturbation D p v) 1 := by
  have hc1 : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d)
      (roughVectorMvConstant (σ := σ) v) 1 := by
    apply rough_vector_constant_weighted
    rw [rough_native_stretched_lie_initial d hd 1 hd]
    exact Submodule.mem_top
  have hc0 := rough_vector_weighted_mono _ (rough_native_stretched_lie_antitone d hd) hc1 (Nat.zero_le 1)
  have he0 : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d)
      ([] : RoughVectorMvPolynomial σ D.E) 0 := fun a ha => False.elim (List.not_mem_nil ha)
  have he1 : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d)
      ([] : RoughVectorMvPolynomial σ D.E) 1 := fun a ha => False.elim (List.not_mem_nil ha)
  exact ⟨native_product_perturbation_polynomial_weighted D d hd hp hp he0 hc0 he1 hc1,
    native_product_perturbation_polynomial_weighted D d hd he0 hc0 hp hp hc1 he1⟩

end Hindman168
