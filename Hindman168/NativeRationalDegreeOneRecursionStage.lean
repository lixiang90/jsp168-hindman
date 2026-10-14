import Hindman168.NativeRationalDegreeOneStateInverse
import Hindman168.NativeRationalWeightedPolynomialFixedGeometry

/-! The actual degree-one node is extracted from the TRUE original weighted
polynomial recursion; its ORIGINAL group/model/lattice/metric remain identical.
The inverse base case is thus usable at the genuine recursive degree-one node. -/

namespace Hindman168
universe u

theorem native_rational_polynomial_state_cast_data {s m n : ℕ} (h : m = n)
    (S : NativeRationalWeightedPolynomialState.{u} s m) : (h ▸ S).1 = S.1 := by
  cases h
  rfl

noncomputable def nativeRationalDegreeOneRecursionStage {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (shifts : ℕ → ℤ) (j : ℕ) (hj : ℓ-j = 1) : NativeRationalWeightedPolynomialState.{u} s 1 :=
  ((native_rational_weighted_polynomial_recursion_bound D F p hp shifts j).trans hj) ▸
    (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts j).2

theorem native_rational_degree_one_recursion_stage_original_data {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (shifts : ℕ → ℤ) (j : ℕ) (hj : ℓ-j = 1) :
    (nativeRationalDegreeOneRecursionStage D F p hp shifts j hj).1 =
      (nativeIteratedRationalWeightedPolynomialReduction D F p hp shifts j).2.1 :=
  native_rational_polynomial_state_cast_data _ _

theorem native_rational_degree_one_recursion_stage_fixed_data {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (shifts : ℕ → ℤ) (j : ℕ) (hj : ℓ-j = 1) :
    (nativeRationalDegreeOneRecursionStage D F p hp shifts j hj).1 =
      (nativeRationalPackedGeometryRecursion D F j).2.1 :=
  (native_rational_degree_one_recursion_stage_original_data D F p hp shifts j hj).trans
    (native_rational_weighted_polynomial_data_fixed D F p hp shifts j)

theorem native_rational_degree_one_last_stage_index (ℓ : ℕ) (hℓ : 0 < ℓ) : ℓ-(ℓ-1) = 1 := by omega

noncomputable def nativeRationalLastDegreeOneStage {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (shifts : ℕ → ℤ) (hℓ : 0 < ℓ) : NativeRationalWeightedPolynomialState.{u} s 1 :=
  nativeRationalDegreeOneRecursionStage D F p hp shifts (ℓ-1) (native_rational_degree_one_last_stage_index ℓ hℓ)

end Hindman168
