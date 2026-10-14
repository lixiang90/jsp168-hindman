import Hindman168.NativeRationalWeightedRelativePolynomialWeights

/-! Real and integer filteredness in the ACTUAL internal relative group;
all native bracket and exponential membership inputs are proved. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_weighted_relative_real_filtered {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) (t : D.G) (h : ℤ) :
    RoughFilteredPolynomial (nativeRationalRelativeInternalGroupLayer D F)
      (fun x : Unit → ℝ => nativeLieExponential (E := (nativeRationalRelativeData D F 1).E)
        (I := (nativeRationalRelativeData D F 1).I) (G := (nativeRationalRelativeData D F 1).G)
        (roughVectorMvEval (E := (nativeRationalRelativeData D F 1).E)
          (nativeRationalWeightedRelativePolynomial D F p hp h0 t h) x)) := by
  apply native_arbitrary_lie_polynomial_filtered (nativeRationalRelativeData D F 1)
    (nativeRelativeRationalLieFiltration D F).layer (nativeRelativeRationalLieFiltration D F).antitone
    (nativeRelativeRationalLieFiltration D F).bracket
  · intro i v hv
    apply (native_rational_relative_internal_logarithm_iff D F i _).mpr
    exact (congrArg (fun z : (nativeRationalRelativeData D F 1).E =>
      z ∈ nativeRationalRelativeLieLayer D F i)
      (nativeLieGlobalLogarithm_exponential (E := (nativeRationalRelativeData D F 1).E)
        (I := (nativeRationalRelativeData D F 1).I) (G := (nativeRationalRelativeData D F 1).G) v)).mpr hv
  · exact native_rational_weighted_relative_polynomial_weighted D F p hp h0 t h

theorem native_rational_weighted_relative_integer_filtered {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) (t : D.G) (h : ℤ) :
    RoughFilteredPolynomial (nativeRationalRelativeInternalGroupLayer D F)
      (nativeRationalWeightedIntegerPair D F p hp h0 t h) := by
  let c : ℤ →+ (Unit → ℝ) := {
    toFun := fun n _ => (n : ℝ)
    map_zero' := by funext j; exact Int.cast_zero
    map_add' := by intro n m; funext j; exact Int.cast_add _ _ }
  have he := rough_filtered_polynomial_precompose _ _
    (native_rational_weighted_relative_real_filtered D F p hp h0 t h) c
  simpa only [c,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
    native_rational_weighted_relative_polynomial_exponential] using he

end Hindman168
