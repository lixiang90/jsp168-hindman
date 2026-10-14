import Hindman168.NativeRationalWeightedOperations
import Hindman168.RoughWeightedPolynomialDifference
import Hindman168.NativeCentralPolynomialProjection

/-! ACTUAL affine progression source preserves TRUE rational filtration
weights/original degree and gives EXACT standard-interval native samples. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalProgressionPolynomial {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (a : ℤ) (P : ℕ) :
    RoughVectorMvPolynomial Unit D.E :=
  roughVectorMvAffineSubstitution (fun _ => (a : ℝ)) (fun _ => (P : ℝ)) p

theorem native_rational_progression_polynomial_weighted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (K : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree K.layer p 0) (a : ℤ) (P : ℕ) :
    RoughVectorMvWeightedDegree K.layer (nativeRationalProgressionPolynomial D p a P) 0 :=
  rough_vector_weighted_affine K.layer K.antitone _ _ hp

theorem native_rational_progression_polynomial_degree {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (d : ℕ)
    (hp : RoughVectorMvDegreeLE p d) (a : ℤ) (P : ℕ) :
    RoughVectorMvDegreeLE (nativeRationalProgressionPolynomial D p a P) d :=
  roughVectorMvAffineSubstitution_degree _ _ hp

theorem native_rational_progression_polynomial_orbit {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (a : ℤ) (P : ℕ) (n : ℤ) :
    nativeMvPolynomialOrbit D (nativeRationalProgressionPolynomial D p a P) (fun _ => n)=
      nativeMvPolynomialOrbit D p (fun _ => a+(P : ℤ)*n) := by
  rw [nativeMvPolynomialOrbit,nativeMvPolynomialOrbit,nativeRationalProgressionPolynomial,
    roughVectorMvAffineSubstitution_eval]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast]

end Hindman168
