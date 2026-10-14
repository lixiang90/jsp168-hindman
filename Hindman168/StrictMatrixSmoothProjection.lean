import Hindman168.UnitriangularExponentialInverse
import Hindman168.MatrixSmoothOperations
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! An actual continuous linear projection onto the strict upper-triangular
matrix subspace. It lets polynomial maps with strict values be treated as
maps into the original normed subspace, without assuming smooth restriction. -/

namespace Hindman168
open Matrix
open scoped ContDiff Matrix.Norms.Elementwise

 noncomputable def strictUpperTriangularProjectionLinear (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] StrictUpperTriangular n ℝ where
  toFun X := ⟨fun i j => if i < j then X i j else 0, by
    intro i j h
    have hij : ¬ i < j := by
      intro hij
      have := Fin.lt_def.mp hij
      omega
    simp only [if_neg hij]⟩
  map_add' X Y := by
    apply Subtype.ext
    ext i j
    by_cases hij : i < j <;> simp [hij]
  map_smul' c X := by
    apply Subtype.ext
    ext i j
    by_cases hij : i < j <;> simp [hij]

 noncomputable def strictUpperTriangularProjection (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] StrictUpperTriangular n ℝ :=
  LinearMap.toContinuousLinearMap (strictUpperTriangularProjectionLinear n)

 theorem strictUpperTriangularProjection_coe {n : ℕ} (X : StrictUpperTriangular n ℝ) :
    strictUpperTriangularProjection n X.val = X := by
  apply Subtype.ext
  ext i j
  change (if i < j then X.val i j else 0) = X.val i j
  by_cases hij : i < j
  · simp only [if_pos hij]
  · have hzero : X.val i j = 0 := X.property i j (by
      have := Fin.le_iff_val_le_val.mp (le_of_not_gt hij)
      omega)
    simp only [if_neg hij, hzero]

 theorem strictUpperTriangularProjection_contDiff {n : ℕ} {r : ℕ∞ω} :
    ContDiff ℝ r (strictUpperTriangularProjection n) :=
  (strictUpperTriangularProjection n).contDiff

end Hindman168
