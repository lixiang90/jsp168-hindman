import Hindman168.RationalCoordinateIntersection
import Hindman168.UnitriangularRationalLieLatticeSpan

/-! Actual rational matrix subspaces and their support intersections.
Flattening is an explicit linear equivalence and commutes with rational
casting. Thus the finite-coordinate intersection theorem applies to matrices
without assuming an adapted basis or a group-lattice compactness theorem. -/

noncomputable section
namespace Hindman168
open Matrix Submodule Set

variable {n : ℕ}

 def matrixCoordinatesLinear (n : ℕ) (R : Type*) [CommRing R] :
    Matrix (Fin n) (Fin n) R ≃ₗ[R] (Fin n × Fin n → R) where
  toFun A p := A p.1 p.2
  invFun x i j := x (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem matrixCoordinatesLinear_rat_cast (A : Matrix (Fin n) (Fin n) ℚ) :
    matrixCoordinatesLinear n ℝ (rationalMatrixCastLinear n A) =
      rationalCoordinateCast (Fin n × Fin n) (matrixCoordinatesLinear n ℚ A) := rfl

 def RationalMatrixSubspace (V : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : Prop :=
  span ℝ ((V : Set _) ∩ ((rationalMatrixCastLinear n).range : Set _)) = V

 theorem matrixCoordinatesLinear_rational_intersection
    (V : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    matrixCoordinatesLinear n ℝ ''
      ((V : Set _) ∩ ((rationalMatrixCastLinear n).range : Set _)) =
    (V.map (matrixCoordinatesLinear n ℝ).toLinearMap : Set _) ∩
      range (rationalCoordinateCast (Fin n × Fin n)) := by
  ext x
  constructor
  · rintro ⟨A, ⟨hA, B, hB⟩, rfl⟩
    refine ⟨⟨A, hA, rfl⟩, matrixCoordinatesLinear n ℚ B, ?_⟩
    rw [← matrixCoordinatesLinear_rat_cast, hB]
  · rintro ⟨⟨A, hA, hAx⟩, q, hqx⟩
    refine ⟨A, ⟨hA, (matrixCoordinatesLinear n ℚ).symm q, ?_⟩, hAx⟩
    apply (matrixCoordinatesLinear n ℝ).injective
    rw [matrixCoordinatesLinear_rat_cast, LinearEquiv.apply_symm_apply, hqx]
    exact hAx.symm

 theorem rationalMatrixSubspace_iff_coordinates
    (V : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    RationalMatrixSubspace V ↔
      RationalCoordinateSubspace (V.map (matrixCoordinatesLinear n ℝ).toLinearMap) := by
  unfold RationalMatrixSubspace RationalCoordinateSubspace
  rw [← matrixCoordinatesLinear_rational_intersection]
  have hs := Submodule.map_span (matrixCoordinatesLinear n ℝ).toLinearMap
    ((V : Set _) ∩ ((rationalMatrixCastLinear n).range : Set _))
  change (span ℝ ((V : Set _) ∩ ((rationalMatrixCastLinear n).range : Set _))).map
      (matrixCoordinatesLinear n ℝ).toLinearMap =
    span ℝ (matrixCoordinatesLinear n ℝ ''
      ((V : Set _) ∩ ((rationalMatrixCastLinear n).range : Set _))) at hs
  rw [← hs]
  exact (Submodule.map_injective_of_injective (matrixCoordinatesLinear n ℝ).injective).eq_iff.symm

 theorem rationalMatrixSubspace_inf
    (V W : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : RationalMatrixSubspace V) (hW : RationalMatrixSubspace W) :
    RationalMatrixSubspace (V ⊓ W) := by
  rw [rationalMatrixSubspace_iff_coordinates,
    Submodule.map_inf _ (matrixCoordinatesLinear n ℝ).injective]
  exact rationalCoordinateSubspace_inf _ _
    ((rationalMatrixSubspace_iff_coordinates V).mp hV)
    ((rationalMatrixSubspace_iff_coordinates W).mp hW)

 def matrixCoordinateZeroSubmodule (n : ℕ) (R : Type*) [CommRing R]
    (p : Fin n → Fin n → Prop) : Submodule R (Matrix (Fin n) (Fin n) R) where
  carrier := {A | ∀ i j, p i j → A i j = 0}
  zero_mem' := by intro i j _; rfl
  add_mem' {A B} hA hB := by
    intro i j hij
    change A i j + B i j = 0
    rw [hA i j hij, hB i j hij, add_zero]
  smul_mem' r A hA := by
    intro i j hij
    change r * A i j = 0
    rw [hA i j hij, mul_zero]

 theorem matrixCoordinatesLinear_coordinateZero (R : Type*) [CommRing R]
    (p : Fin n → Fin n → Prop) :
    (matrixCoordinateZeroSubmodule n R p).map (matrixCoordinatesLinear n R).toLinearMap =
      coordinateZeroSubmodule R (fun q : Fin n × Fin n => p q.1 q.2) := by
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩ ⟨i, j⟩ hij
    exact hA i j hij
  · intro hx
    refine ⟨(matrixCoordinatesLinear n R).symm x, ?_,
      LinearEquiv.apply_symm_apply _ _⟩
    intro i j hij
    exact hx (i, j) hij

 theorem rationalMatrixSubspace_coordinateZero (p : Fin n → Fin n → Prop) :
    RationalMatrixSubspace (matrixCoordinateZeroSubmodule n ℝ p) := by
  rw [rationalMatrixSubspace_iff_coordinates, matrixCoordinatesLinear_coordinateZero]
  exact rationalCoordinateSubspace_coordinateZero _

 def matrixDepthSubmodule (n k : ℕ) (R : Type*) [CommRing R] :
    Submodule R (Matrix (Fin n) (Fin n) R) :=
  matrixCoordinateZeroSubmodule n R (fun i j => j.val < i.val + k)

 theorem matrixDepthSubmodule_mem_iff (R : Type*) [CommRing R]
    (k : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    A ∈ matrixDepthSubmodule n k R ↔ MatrixDepth k A := Iff.rfl

 theorem rationalMatrixSubspace_depth (k : ℕ) :
    RationalMatrixSubspace (matrixDepthSubmodule n k ℝ) :=
  rationalMatrixSubspace_coordinateZero _

end Hindman168
