import Hindman168.UnitriangularFiniteExponential

/-! An actual inverse to the nilpotent matrix exponential. The residual
correction X <- X+(g-exp X) improves support by one superdiagonal at each
step, hence terminates in a number of steps bounded by matrix dimension.
No formal logarithm identity, BCH formula or bijectivity is assumed. -/

namespace Hindman168
open Matrix

variable {n : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]

 noncomputable def unitriangularLogIteration (g : Unitriangular n R) :
    ℕ → Matrix (Fin n) (Fin n) R
  | 0 => 0
  | r + 1 => unitriangularLogIteration g r +
      ((g.val : Matrix (Fin n) (Fin n) R) - matrixFiniteExp (unitriangularLogIteration g r))

 theorem unitriangularLogIteration_strict (g : Unitriangular n R) (r : ℕ) :
    MatrixDepth 1 (unitriangularLogIteration g r) := by
  induction r with
  | zero => exact matrixDepth_zero 1
  | succ r ih =>
    exact ih.add (matrixDepth_unitriangular_difference g.property (matrixFiniteExp_unitriangular ih))

 theorem unitriangularLogIteration_residual_depth (g : Unitriangular n R) (r : ℕ) :
    MatrixDepth (r + 1) ((g.val : Matrix (Fin n) (Fin n) R) -
      matrixFiniteExp (unitriangularLogIteration g r)) := by
  induction r with
  | zero =>
    simp only [unitriangularLogIteration, matrixFiniteExp_zero]
    exact (matrixDepth_sub_one_iff_unitriangular _).mpr g.property
  | succ r ih =>
    let A := unitriangularLogIteration g r
    let D := (g.val : Matrix (Fin n) (Fin n) R) - matrixFiniteExp A
    let Y := A + D
    have hA : MatrixDepth 1 A := unitriangularLogIteration_strict g r
    have hY : MatrixDepth 1 Y := unitriangularLogIteration_strict g (r + 1)
    have hdiff : MatrixDepth (r + 1) (Y - A) := by
      simpa only [Y, add_sub_cancel_left] using ih
    have hgain := matrixFiniteExp_difference_depth hY hA hdiff
    have heq : (g.val : Matrix (Fin n) (Fin n) R) - matrixFiniteExp Y =
        -(matrixFiniteExp Y - matrixFiniteExp A - (Y - A)) := by
      dsimp [Y, D]
      abel
    change MatrixDepth (r + 1 + 1) ((g.val : Matrix (Fin n) (Fin n) R) - matrixFiniteExp Y)
    rw [heq]
    exact hgain.neg

 noncomputable def unitriangularLogMatrix (g : Unitriangular n R) : Matrix (Fin n) (Fin n) R :=
  unitriangularLogIteration g n

 theorem unitriangularLogMatrix_strict (g : Unitriangular n R) :
    MatrixDepth 1 (unitriangularLogMatrix g) := unitriangularLogIteration_strict g n

 theorem matrixFiniteExp_logMatrix (g : Unitriangular n R) :
    matrixFiniteExp (unitriangularLogMatrix g) = (g.val : Matrix (Fin n) (Fin n) R) := by
  exact (sub_eq_zero.mp ((unitriangularLogIteration_residual_depth g n).eq_zero (by omega))).symm

 def StrictUpperTriangular (n : ℕ) (R : Type*) [CommRing R] :
    Submodule R (Matrix (Fin n) (Fin n) R) where
  carrier := {A | MatrixDepth 1 A}
  zero_mem' := matrixDepth_zero 1
  add_mem' hA hB := hA.add hB
  smul_mem' c _ hA := hA.smul c

 noncomputable def unitriangularExponential (A : StrictUpperTriangular n R) : Unitriangular n R :=
  unitriangularOfMatrix (matrixFiniteExp A.val) (matrixFiniteExp_unitriangular A.property)

 noncomputable def unitriangularLogarithm (g : Unitriangular n R) : StrictUpperTriangular n R :=
  ⟨unitriangularLogMatrix g, unitriangularLogMatrix_strict g⟩

 theorem unitriangularExponential_value (A : StrictUpperTriangular n R) :
    ((unitriangularExponential A).val : Matrix (Fin n) (Fin n) R) = IsNilpotent.exp A.val :=
  matrixFiniteExp_eq_exp A.property

 theorem unitriangularExponential_logarithm (g : Unitriangular n R) :
    unitriangularExponential (unitriangularLogarithm g) = g := by
  apply unitriangular_val_injective
  exact matrixFiniteExp_logMatrix g

 theorem unitriangularLogarithm_exponential (A : StrictUpperTriangular n R) :
    unitriangularLogarithm (unitriangularExponential A) = A := by
  apply Subtype.ext
  apply matrixFiniteExp_injective (unitriangularLogMatrix_strict _) A.property
  exact matrixFiniteExp_logMatrix (unitriangularExponential A)

 noncomputable def unitriangularExponentialEquiv : StrictUpperTriangular n R ≃ Unitriangular n R where
  toFun := unitriangularExponential
  invFun := unitriangularLogarithm
  left_inv := unitriangularLogarithm_exponential
  right_inv := unitriangularExponential_logarithm

 theorem unitriangularExponential_add_of_commute (A B : StrictUpperTriangular n R)
    (hAB : Commute A.val B.val) :
    unitriangularExponential (A + B) = unitriangularExponential A * unitriangularExponential B := by
  apply unitriangular_val_injective
  change matrixFiniteExp (A.val + B.val) = matrixFiniteExp A.val * matrixFiniteExp B.val
  rw [matrixFiniteExp_eq_exp (A.property.add B.property), matrixFiniteExp_eq_exp A.property,
    matrixFiniteExp_eq_exp B.property]
  exact IsNilpotent.exp_add_of_commute hAB A.property.nilpotent B.property.nilpotent

 theorem unitriangularExponential_neg (A : StrictUpperTriangular n R) :
    unitriangularExponential (-A) = (unitriangularExponential A)⁻¹ := by
  apply Eq.symm
  apply inv_eq_of_mul_eq_one_right
  apply unitriangular_val_injective
  change matrixFiniteExp A.val * matrixFiniteExp (-A.val) = 1
  rw [matrixFiniteExp_eq_exp A.property, matrixFiniteExp_eq_exp A.property.neg]
  exact IsNilpotent.exp_mul_exp_neg_self A.property.nilpotent

end Hindman168
