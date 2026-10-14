import Hindman168.NativeRationalWeightedPolynomialRecursion

/-! ALL actual recursive groups/models/lattices/charts/metrics/filtrations
are fixed BEFORE source coefficients and integer shift choices. Polynomial
normalizations cannot change the native geometric data at any stage. -/

namespace Hindman168
universe u

abbrev NativeRationalPackedGeometry (s : ℕ) :=
  Σ ℓ : ℕ, Σ D : NativeNilmanifoldData.{u} s, NativeRationalLieFiltration D ℓ

noncomputable def nativeRationalPackedGeometryStep {s : ℕ} (S : NativeRationalPackedGeometry.{u} s) :
    NativeRationalPackedGeometry.{u} s :=
  ⟨S.1-1,nativeRationalDegreeReducedData S.2.1 S.2.2,nativeDegreeReducedRationalLieFiltration S.2.1 S.2.2⟩

noncomputable def nativeRationalPackedGeometryRecursion {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) : ℕ → NativeRationalPackedGeometry.{u} s
  | 0 => ⟨ℓ,D,F⟩
  | n+1 => nativeRationalPackedGeometryStep (nativeRationalPackedGeometryRecursion D F n)

def nativeRationalWeightedPolynomialGeometry {s : ℕ}
    (S : Σ ℓ : ℕ, NativeRationalWeightedPolynomialState.{u} s ℓ) : NativeRationalPackedGeometry.{u} s :=
  ⟨S.1,S.2.1,S.2.2.1⟩

theorem native_rational_weighted_polynomial_fixed_geometry {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (shifts : ℕ → ℤ) (n : ℕ) :
    nativeRationalWeightedPolynomialGeometry (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts n) =
      nativeRationalPackedGeometryRecursion D F n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change nativeRationalPackedGeometryStep
        (nativeRationalWeightedPolynomialGeometry (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts n)) =
        nativeRationalPackedGeometryStep (nativeRationalPackedGeometryRecursion D F n)
      exact congrArg nativeRationalPackedGeometryStep ih

theorem native_rational_weighted_polynomial_data_fixed {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (shifts : ℕ → ℤ) (n : ℕ) :
    (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts n).2.1 =
      (nativeRationalPackedGeometryRecursion D F n).2.1 :=
  congrArg (fun S : NativeRationalPackedGeometry.{u} s => S.2.1)
    (native_rational_weighted_polynomial_fixed_geometry D F p hp shifts n)

theorem native_rational_weighted_polynomial_geometry_independent {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p q : RoughVectorMvPolynomial Unit D.E)
    (hp : RoughVectorMvWeightedDegree F.layer p 0) (hq : RoughVectorMvWeightedDegree F.layer q 0)
    (shifts shifts' : ℕ → ℤ) (n : ℕ) :
    nativeRationalWeightedPolynomialGeometry (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts n) =
      nativeRationalWeightedPolynomialGeometry (nativeIteratedRationalWeightedPolynomialReduction D F q hq shifts' n) :=
  (native_rational_weighted_polynomial_fixed_geometry D F p hp shifts n).trans
    (native_rational_weighted_polynomial_fixed_geometry D F q hq shifts' n).symm

end Hindman168
