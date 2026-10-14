import Hindman168.NativeBasepointAmbientPairPolynomial
import Hindman168.RoughVectorSubmodulePolynomial
import Hindman168.NativeCentralPolynomialProjection

/-! A genuine polynomial in the SAME ACTUAL relative native model for
the original normalized shifted pair. ALL coefficient-membership inputs
are proved from actual original samples, not assumed as an interface. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeBasepointRelativePolynomial {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) : RoughVectorMvPolynomial Unit (nativeRelativeSquareData D d hd 1).E :=
  roughVectorMvSubmodulePolynomial (nativeLieSubalgebraModel (nativeRelativeSquareNativeLieAlgebra D d 1))
    (nativeBasepointAmbientPairPolynomial D p r t h)
    (native_basepoint_ambient_pair_coefficient_mem D d hd p hp r t h)

theorem native_basepoint_relative_polynomial_inclusion {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) :
    roughVectorMvLinearMap (nativeRelativeModelInclusion D d hd 1).toLinearMap
      (nativeBasepointRelativePolynomial D d hd p hp r t h) =
      roughVectorMvCollect (nativeBasepointAmbientPairPolynomial D p r t h) :=
  rough_vector_submodule_polynomial_inclusion _ _ _

theorem native_basepoint_relative_polynomial_degree {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) : RoughVectorMvDegreeLE (nativeBasepointRelativePolynomial D d hd p hp r t h) (s*d) :=
  rough_vector_submodule_polynomial_degree _ _ _ (native_basepoint_ambient_pair_degree D d hd p hp r t h)

theorem native_basepoint_relative_polynomial_eval {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) (x : Unit → ℝ) :
    nativeRelativeModelInclusion D d hd 1
      (roughVectorMvEval (E := (nativeRelativeSquareData D d hd 1).E)
        (nativeBasepointRelativePolynomial D d hd p hp r t h) x) =
      roughVectorMvEval (E := D.E × D.E) (nativeBasepointAmbientPairPolynomial D p r t h) x := by
  have he := roughVectorMvLinearMap_eval (nativeRelativeModelInclusion D d hd 1).toLinearMap
    (nativeBasepointRelativePolynomial D d hd p hp r t h) x
  rw [native_basepoint_relative_polynomial_inclusion,rough_vector_collect_eval] at he
  exact he.symm

theorem native_basepoint_relative_polynomial_projection {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) (ell : D.E × D.E →ₗ[ℝ] ℝ) :
    roughVectorMvProjection (ell.comp (nativeRelativeModelInclusion D d hd 1).toLinearMap)
      (nativeBasepointRelativePolynomial D d hd p hp r t h) =
      roughVectorMvProjection ell (nativeBasepointAmbientPairPolynomial D p r t h) := by
  rw [← roughVectorMvProjection_linearMap,native_basepoint_relative_polynomial_inclusion,rough_vector_collect_projection]

theorem native_basepoint_relative_polynomial_coeff {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) (J : Unit →₀ ℕ) :
    nativeRelativeModelInclusion D d hd 1
      (roughVectorMvCoefficient (nativeBasepointRelativePolynomial D d hd p hp r t h) J) =
      roughVectorMvCoefficient (nativeBasepointAmbientPairPolynomial D p r t h) J := by
  have he := rough_vector_coefficient_linear_map (nativeRelativeModelInclusion D d hd 1).toLinearMap
    (nativeBasepointRelativePolynomial D d hd p hp r t h) J
  rw [native_basepoint_relative_polynomial_inclusion,rough_vector_collect_coefficient] at he
  exact he.symm

theorem native_basepoint_relative_polynomial_exponential {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h n : ℤ) :
    nativeLieExponential (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G)
      (roughVectorMvEval (E := (nativeRelativeSquareData D d hd 1).E)
        (nativeBasepointRelativePolynomial D d hd p hp r t h) (fun _ => (n : ℝ))) =
      nativeBasepointRelativeIntegerPair D d hd p hp r t h n := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  have he := native_relative_data_exponential D d hd 1
    (roughVectorMvEval (E := (nativeRelativeSquareData D d hd 1).E)
      (nativeBasepointRelativePolynomial D d hd p hp r t h) (fun _ => (n : ℝ)))
  rw [native_basepoint_relative_polynomial_eval,native_basepoint_ambient_pair_integer_log D d hd p hp r t h n,
    nativeLieExponential_globalLogarithm] at he
  exact Subtype.ext he

theorem native_basepoint_relative_polynomial_orbit {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h n : ℤ) :
    nativeMvPolynomialOrbit (nativeRelativeSquareData D d hd 1)
      (nativeBasepointRelativePolynomial D d hd p hp r t h) (fun _ => n) =
      (nativeBasepointRelativeIntegerPair D d hd p hp r t h n :
        (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ) := by
  unfold nativeMvPolynomialOrbit
  rw [native_basepoint_relative_polynomial_exponential]

end Hindman168
