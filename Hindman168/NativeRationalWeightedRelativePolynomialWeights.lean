import Hindman168.NativeRationalWeightedPairDifferencePolynomial
import Hindman168.NativeRationalWeightedRelativePolynomial
import Hindman168.NativeRationalRelativeRationalFiltration
import Hindman168.RoughVectorZeroTrim

/-! ACTUAL original relative coefficient polynomial has SAME genuine
relative filtration weights. The extra first-minus-second coefficient
layer is proved by actual weighted product/shift perturbation. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_weighted_pair_next_layer_coefficient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (t : D.G) (h : ℤ) (J : Unit →₀ ℕ) :
    roughVectorMvCoefficient (nativeRationalWeightedShiftPolynomial D p t h) J-
      roughVectorMvCoefficient (p) J ∈
      F.layer (J.sum (fun _ n => n)+1) := by
  have he := rough_vector_coefficient_difference_of_eval (nativeRationalWeightedPairDifferencePolynomial D p t h)
    (nativeRationalWeightedShiftPolynomial D p t h) (p)
    (native_rational_weighted_pair_difference_eval D p t h) J
  rw [← he]
  exact rough_vector_weighted_coefficient _ F.antitone
    (native_rational_weighted_pair_difference_weighted D F p hp t h) J

theorem native_rational_weighted_ambient_pair_coefficient_components {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (t : D.G) (h : ℤ) (J : Unit →₀ ℕ) :
    roughVectorMvCoefficient (nativeRationalWeightedAmbientPairPolynomial D p t h) J =
      (roughVectorMvCoefficient (nativeRationalWeightedShiftPolynomial D p t h) J,
        roughVectorMvCoefficient (p) J) := by
  rw [nativeRationalWeightedAmbientPairPolynomial,rough_vector_coefficient_append,
    rough_vector_coefficient_linear_map,rough_vector_coefficient_linear_map]
  simp only [LinearMap.inl_apply,LinearMap.inr_apply,Prod.mk_add_mk,add_zero,zero_add]

theorem native_rational_weighted_ambient_pair_coefficient_layer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (t : D.G) (h : ℤ) (J : Unit →₀ ℕ) :
    roughVectorMvCoefficient (nativeRationalWeightedAmbientPairPolynomial D p t h) J ∈
      relativeLinearFiltration F.layer (J.sum (fun _ n => n)) := by
  rw [native_rational_weighted_ambient_pair_coefficient_components]
  apply (relative_linear_model_mem_iff _ _ _).mpr
  refine ⟨?_,?_,native_rational_weighted_pair_next_layer_coefficient D F p hp t h J⟩
  · simpa only [Nat.add_zero] using rough_vector_weighted_coefficient F.layer F.antitone
      (native_rational_weighted_shift_polynomial_weighted D F hp t h) J
  · simpa only [Nat.add_zero] using rough_vector_weighted_coefficient F.layer F.antitone hp J

theorem native_rational_weighted_relative_polynomial_weighted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0)
    (t : D.G) (h : ℤ) :
    RoughVectorMvWeightedDegree (nativeRationalRelativeLieLayer D F)
      (nativeRationalWeightedRelativePolynomial D F p hp h0 t h) 0 := by
  rintro a ha
  change a ∈ (roughVectorMvSupport (nativeRationalWeightedAmbientPairPolynomial D p t h)).toList.map
    (fun J => (MvPolynomial.monomial J 1,
      (⟨roughVectorMvCoefficient (nativeRationalWeightedAmbientPairPolynomial D p t h) J,
        native_rational_weighted_ambient_pair_coefficient_mem D F p hp h0 t h J⟩ :
        (nativeRationalRelativeData D F 1).E))) at ha
  obtain ⟨J,_,rfl⟩ := List.mem_map.mp ha
  rw [MvPolynomial.totalDegree_monomial J one_ne_zero,Nat.add_zero]
  change roughVectorMvCoefficient (nativeRationalWeightedAmbientPairPolynomial D p t h) J ∈
    relativeLinearFiltration F.layer (J.sum (fun _ n => n))
  exact native_rational_weighted_ambient_pair_coefficient_layer D F p hp t h J

theorem native_rational_weighted_relative_zero_trim_degree {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) (t : D.G) (h : ℤ) :
    RoughVectorMvDegreeLE (roughVectorMvZeroTrim (nativeRationalWeightedRelativePolynomial D F p hp h0 t h)) ℓ := by
  have he := rough_vector_zero_trim_degree (nativeRelativeRationalLieFiltration D F).layer
    (nativeRelativeRationalLieFiltration D F).antitone
    (native_rational_weighted_relative_polynomial_weighted D F p hp h0 t h)
    (nativeRelativeRationalLieFiltration D F).terminal
  simpa only [Nat.sub_zero] using he

end Hindman168
