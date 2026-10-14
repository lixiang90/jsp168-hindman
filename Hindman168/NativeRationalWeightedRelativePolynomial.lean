import Hindman168.NativeRationalWeightedAmbientPairPolynomial
import Hindman168.RoughVectorSubmodulePolynomial
import Hindman168.NativeCentralPolynomialProjection

/-! A genuine polynomial in the SAME ACTUAL relative native model for
the original normalized shifted pair. ALL coefficient-membership inputs
are proved from actual original samples, not assumed as an interface. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalWeightedRelativePolynomial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0)
    (t : D.G) (h : ℤ) : RoughVectorMvPolynomial Unit (nativeRationalRelativeData D F 1).E :=
  roughVectorMvSubmodulePolynomial (nativeLieSubalgebraModel (nativeRationalRelativeNativeSubalgebra D F 1))
    (nativeRationalWeightedAmbientPairPolynomial D p t h)
    (native_rational_weighted_ambient_pair_coefficient_mem D F p hp h0 t h)

theorem native_rational_weighted_relative_polynomial_inclusion {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0)
    (t : D.G) (h : ℤ) :
    roughVectorMvLinearMap (nativeRationalRelativeModelInclusion D F 1).toLinearMap
      (nativeRationalWeightedRelativePolynomial D F p hp h0 t h) =
      roughVectorMvCollect (nativeRationalWeightedAmbientPairPolynomial D p t h) :=
  rough_vector_submodule_polynomial_inclusion _ _ _

theorem native_rational_weighted_relative_polynomial_eval {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0)
    (t : D.G) (h : ℤ) (x : Unit → ℝ) :
    nativeRationalRelativeModelInclusion D F 1
      (roughVectorMvEval (E := (nativeRationalRelativeData D F 1).E)
        (nativeRationalWeightedRelativePolynomial D F p hp h0 t h) x) =
      roughVectorMvEval (E := D.E × D.E) (nativeRationalWeightedAmbientPairPolynomial D p t h) x := by
  have he := roughVectorMvLinearMap_eval (nativeRationalRelativeModelInclusion D F 1).toLinearMap
    (nativeRationalWeightedRelativePolynomial D F p hp h0 t h) x
  rw [native_rational_weighted_relative_polynomial_inclusion,rough_vector_collect_eval] at he
  exact he.symm

theorem native_rational_weighted_relative_polynomial_projection {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0)
    (t : D.G) (h : ℤ) (ell : D.E × D.E →ₗ[ℝ] ℝ) :
    roughVectorMvProjection (ell.comp (nativeRationalRelativeModelInclusion D F 1).toLinearMap)
      (nativeRationalWeightedRelativePolynomial D F p hp h0 t h) =
      roughVectorMvProjection ell (nativeRationalWeightedAmbientPairPolynomial D p t h) := by
  rw [← roughVectorMvProjection_linearMap,native_rational_weighted_relative_polynomial_inclusion,rough_vector_collect_projection]

theorem native_rational_weighted_relative_polynomial_coeff {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0)
    (t : D.G) (h : ℤ) (J : Unit →₀ ℕ) :
    nativeRationalRelativeModelInclusion D F 1
      (roughVectorMvCoefficient (nativeRationalWeightedRelativePolynomial D F p hp h0 t h) J) =
      roughVectorMvCoefficient (nativeRationalWeightedAmbientPairPolynomial D p t h) J := by
  have he := rough_vector_coefficient_linear_map (nativeRationalRelativeModelInclusion D F 1).toLinearMap
    (nativeRationalWeightedRelativePolynomial D F p hp h0 t h) J
  rw [native_rational_weighted_relative_polynomial_inclusion,rough_vector_collect_coefficient] at he
  exact he.symm

theorem native_rational_weighted_relative_polynomial_exponential {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0)
    (t : D.G) (h n : ℤ) :
    nativeLieExponential (E := (nativeRationalRelativeData D F 1).E)
      (I := (nativeRationalRelativeData D F 1).I) (G := (nativeRationalRelativeData D F 1).G)
      (roughVectorMvEval (E := (nativeRationalRelativeData D F 1).E)
        (nativeRationalWeightedRelativePolynomial D F p hp h0 t h) (fun _ => (n : ℝ))) =
      nativeRationalWeightedIntegerPair D F p hp h0 t h n := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  have he := native_rational_relative_data_exponential D F 1
    (roughVectorMvEval (E := (nativeRationalRelativeData D F 1).E)
      (nativeRationalWeightedRelativePolynomial D F p hp h0 t h) (fun _ => (n : ℝ)))
  rw [native_rational_weighted_relative_polynomial_eval,native_rational_weighted_ambient_pair_integer_log D F p hp h0 t h n,
    nativeLieExponential_globalLogarithm] at he
  exact Subtype.ext he

theorem native_rational_weighted_relative_polynomial_orbit {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0)
    (t : D.G) (h n : ℤ) :
    nativeMvPolynomialOrbit (nativeRationalRelativeData D F 1)
      (nativeRationalWeightedRelativePolynomial D F p hp h0 t h) (fun _ => n) =
      (nativeRationalWeightedIntegerPair D F p hp h0 t h n :
        (nativeRationalRelativeData D F 1).G ⧸ (nativeRationalRelativeData D F 1).Γ) := by
  unfold nativeMvPolynomialOrbit
  rw [native_rational_weighted_relative_polynomial_exponential]

end Hindman168
