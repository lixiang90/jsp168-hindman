import Hindman168.NativeBasepointPairDifferencePolynomial
import Hindman168.NativeBasepointRelativePolynomial
import Hindman168.NativeRelativeLieFiltration

/-! ACTUAL original relative coefficient polynomial has SAME genuine
relative filtration weights. The extra first-minus-second coefficient
layer is proved by actual weighted product/shift perturbation. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_basepoint_pair_next_layer_coefficient {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) (J : Unit →₀ ℕ) :
    roughVectorMvCoefficient (nativeBasepointShiftPolynomial D p r t h) J-
      roughVectorMvCoefficient (nativeBasepointPolynomial D p r) J ∈
      roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d (J.sum (fun _ n => n)+1) := by
  have he := rough_vector_coefficient_difference_of_eval (nativeBasepointPairDifferencePolynomial D p r t h)
    (nativeBasepointShiftPolynomial D p r t h) (nativeBasepointPolynomial D p r)
    (native_basepoint_pair_difference_eval D p r t h) J
  rw [← he]
  exact rough_vector_weighted_coefficient _ (rough_native_stretched_lie_antitone d hd)
    (native_basepoint_pair_difference_weighted D d hd p hp r t h) J

theorem native_basepoint_ambient_pair_coefficient_components {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (r t : D.G) (h : ℤ) (J : Unit →₀ ℕ) :
    roughVectorMvCoefficient (nativeBasepointAmbientPairPolynomial D p r t h) J =
      (roughVectorMvCoefficient (nativeBasepointShiftPolynomial D p r t h) J,
        roughVectorMvCoefficient (nativeBasepointPolynomial D p r) J) := by
  rw [nativeBasepointAmbientPairPolynomial,rough_vector_coefficient_append,
    rough_vector_coefficient_linear_map,rough_vector_coefficient_linear_map]
  simp only [LinearMap.inl_apply,LinearMap.inr_apply,Prod.mk_add_mk,add_zero,zero_add]

theorem native_basepoint_ambient_pair_coefficient_layer {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) (J : Unit →₀ ℕ) :
    roughVectorMvCoefficient (nativeBasepointAmbientPairPolynomial D p r t h) J ∈
      nativeRelativeSquareModel D d (J.sum (fun _ n => n)) := by
  rw [native_basepoint_ambient_pair_coefficient_components,
    ← native_relative_ambient_lie_layer_eq D d (J.sum (fun _ n => n))]
  apply (relative_linear_model_mem_iff _ _ _).mpr
  refine ⟨?_,?_,native_basepoint_pair_next_layer_coefficient D d hd p hp r t h J⟩
  · have hw := rough_vector_zero_trim_weighted _ (native_basepoint_shift_raw_weighted D d hd p hp r t h)
    simpa only [nativeBasepointShiftPolynomial,Nat.add_zero] using
      rough_vector_weighted_coefficient _ (rough_native_stretched_lie_antitone d hd) hw J
  · simpa only [Nat.add_zero] using rough_vector_weighted_coefficient _ (rough_native_stretched_lie_antitone d hd)
      (native_basepoint_polynomial_weighted D d hd p hp r) J

theorem native_basepoint_relative_polynomial_weighted {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) :
    RoughVectorMvWeightedDegree (nativeRelativeLieFiltration D d hd)
      (nativeBasepointRelativePolynomial D d hd p hp r t h) 0 := by
  rintro a ha
  change a ∈ (roughVectorMvSupport (nativeBasepointAmbientPairPolynomial D p r t h)).toList.map
    (fun J => (MvPolynomial.monomial J 1,
      (⟨roughVectorMvCoefficient (nativeBasepointAmbientPairPolynomial D p r t h) J,
        native_basepoint_ambient_pair_coefficient_mem D d hd p hp r t h J⟩ :
        (nativeRelativeSquareData D d hd 1).E))) at ha
  obtain ⟨J,_,rfl⟩ := List.mem_map.mp ha
  rw [MvPolynomial.totalDegree_monomial J one_ne_zero,Nat.add_zero]
  change roughVectorMvCoefficient (nativeBasepointAmbientPairPolynomial D p r t h) J ∈
    nativeRelativeSquareModel D d (J.sum (fun _ n => n))
  exact native_basepoint_ambient_pair_coefficient_layer D d hd p hp r t h J

end Hindman168
