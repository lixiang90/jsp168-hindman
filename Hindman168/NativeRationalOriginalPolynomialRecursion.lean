import Hindman168.NativeRationalWeightedPolynomialRecursion
import Hindman168.NativeRationalCompactHorizontalPolynomial

/-! Actual finite POLYNOMIAL recursion applied to the ORIGINAL ordinary
degree <=d source, retaining SAME original stretch d at its input. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeOriginalRationalPolynomialRecursion {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d) (shifts : ℕ → ℤ) (n : ℕ) :
    Σ m : ℕ, NativeRationalWeightedPolynomialState.{u} s m :=
  nativeIteratedRationalWeightedPolynomialReduction D (nativeOriginalRationalLieFiltration D d hd) p
    (rough_native_weighted_polynomial_initial d hd hp) shifts n

theorem native_original_rational_polynomial_recursion_bound {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d) (shifts : ℕ → ℤ) (n : ℕ) :
    (nativeOriginalRationalPolynomialRecursion D d hd p hp shifts n).1 = s*d-n :=
  native_rational_weighted_polynomial_recursion_bound D (nativeOriginalRationalLieFiltration D d hd) p
    (rough_native_weighted_polynomial_initial d hd hp) shifts n

theorem native_original_rational_polynomial_recursion_degree {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d) (shifts : ℕ → ℤ) (n : ℕ) :
    RoughVectorMvDegreeLE (nativeOriginalRationalPolynomialRecursion D d hd p hp shifts n).2.2.2.val (s*d-n) :=
  native_rational_weighted_polynomial_recursion_degree D (nativeOriginalRationalLieFiltration D d hd) p
    (rough_native_weighted_polynomial_initial d hd hp) shifts n

theorem native_original_rational_polynomial_recursion_initial_sample {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d) (shifts : ℕ → ℤ) (x : Unit → ℤ) :
    nativeMvPolynomialOrbit D (nativeOriginalRationalPolynomialRecursion D d hd p hp shifts 0).2.2.2.val x =
      nativeMvPolynomialOrbit D p x :=
  native_rational_weighted_polynomial_initial_sample D (nativeOriginalRationalLieFiltration D d hd) p
    (rough_native_weighted_polynomial_initial d hd hp) x

theorem native_original_rational_polynomial_recursion_terminal {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d) (shifts : ℕ → ℤ) :
    Subsingleton (nativeOriginalRationalPolynomialRecursion D d hd p hp shifts (s*d)).2.1.G :=
  native_rational_weighted_polynomial_recursion_terminal_group D (nativeOriginalRationalLieFiltration D d hd) p
    (rough_native_weighted_polynomial_initial d hd hp) shifts

end Hindman168
