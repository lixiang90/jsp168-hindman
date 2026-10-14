import Hindman168.MatrixPolynomialSupport
import Hindman168.NilpotentPolynomialExponentialCurve

/-! The actual BCH curve is the proved unitriangular logarithm of the
actual product exp(t*A)*exp(t*B), computed over the polynomial coefficient
ring. Evaluation commutes with the original exp/log maps, so its endpoint
is the original noncommuting product logarithm. Lie membership of the
logarithm coefficients remains to be derived from its differential equation. -/

noncomputable section
namespace Hindman168
open Matrix Polynomial

variable {n : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]
local instance bchCurveMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) R) :=
  LieRing.ofAssociativeRing

 def matrixPolynomialEval (r : R) :
    Polynomial (Matrix (Fin n) (Fin n) R) →+* Matrix (Fin n) (Fin n) R :=
  (Polynomial.evalRingHom r).mapMatrix.comp (matPolyEquiv (R := R)).symm.toRingHom

 def unitriangularPolynomialScale (A : StrictUpperTriangular n R) :
    StrictUpperTriangular n (Polynomial R) :=
  ⟨(matPolyEquiv (R := R)).symm (monomial 1 A.val),
    (matrixPolynomialDepth_iff _ _).mp (matrixPolynomialDepth_monomial A.property 1)⟩

 def unitriangularPolynomialProductCurve (A B : StrictUpperTriangular n R) :
    Unitriangular n (Polynomial R) :=
  unitriangularExponential (unitriangularPolynomialScale A) *
    unitriangularExponential (unitriangularPolynomialScale B)

 def unitriangularPolynomialBCHCurve (A B : StrictUpperTriangular n R) :
    Polynomial (Matrix (Fin n) (Fin n) R) :=
  matPolyEquiv (unitriangularLogarithm (unitriangularPolynomialProductCurve A B)).val

 omit [Algebra ℚ R] in
 theorem matrixPolynomialEval_zero_coeff (p : Polynomial (Matrix (Fin n) (Fin n) R)) :
    matrixPolynomialEval 0 p = p.coeff 0 := by
  ext i j
  change ((matPolyEquiv (R := R)).symm p i j).eval 0 = p.coeff 0 i j
  rw [← Polynomial.coeff_zero_eq_eval_zero, matPolyEquiv_symm_apply_coeff]

 omit [Algebra ℚ R] in
 theorem unitriangularPolynomialScale_entry (A : StrictUpperTriangular n R) (i j : Fin n) :
    (unitriangularPolynomialScale A).val i j = monomial 1 (A.val i j) := by
  apply Polynomial.ext
  intro k
  change ((matPolyEquiv (R := R)).symm (monomial 1 A.val) i j).coeff k = _
  rw [matPolyEquiv_symm_apply_coeff, coeff_monomial, coeff_monomial]
  split_ifs <;> rfl

 omit [Algebra ℚ R] in
 theorem unitriangularPolynomialScale_eval (A : StrictUpperTriangular n R) (r : R) :
    strictUpperTriangularMap (Polynomial.evalRingHom r) (unitriangularPolynomialScale A) = r • A := by
  apply Subtype.ext
  ext i j
  change ((unitriangularPolynomialScale A).val i j).eval r = r * A.val i j
  rw [unitriangularPolynomialScale_entry, eval_monomial, pow_one, mul_comm]

 theorem unitriangularPolynomialProductCurve_eval (A B : StrictUpperTriangular n R) (r : R) :
    unitriangularMap (Polynomial.evalRingHom r) (unitriangularPolynomialProductCurve A B) =
      unitriangularExponential (r • A) * unitriangularExponential (r • B) := by
  unfold unitriangularPolynomialProductCurve
  rw [map_mul, unitriangularExponential_map, unitriangularExponential_map,
    unitriangularPolynomialScale_eval, unitriangularPolynomialScale_eval]

 theorem unitriangularPolynomialBCHCurve_eval (A B : StrictUpperTriangular n R) (r : R) :
    matrixPolynomialEval r (unitriangularPolynomialBCHCurve A B) =
      (unitriangularLogarithm (unitriangularExponential (r • A) * unitriangularExponential (r • B))).val := by
  change (Polynomial.evalRingHom r).mapMatrix
    ((matPolyEquiv (R := R)).symm
      (matPolyEquiv (unitriangularLogarithm (unitriangularPolynomialProductCurve A B)).val)) = _
  rw [AlgEquiv.symm_apply_apply]
  change (strictUpperTriangularMap (Polynomial.evalRingHom r)
    (unitriangularLogarithm (unitriangularPolynomialProductCurve A B))).val = _
  rw [unitriangularLogarithm_map, unitriangularPolynomialProductCurve_eval]

 theorem unitriangularPolynomialBCHCurve_constant_zero (A B : StrictUpperTriangular n R) :
    (unitriangularPolynomialBCHCurve A B).coeff 0 = 0 := by
  rw [← matrixPolynomialEval_zero_coeff, unitriangularPolynomialBCHCurve_eval]
  have hE : unitriangularExponential (0 : StrictUpperTriangular n R) = 1 := by
    apply unitriangular_val_injective
    exact matrixFiniteExp_zero
  simp only [zero_smul, hE, one_mul]
  have hL : unitriangularLogarithm (1 : Unitriangular n R) = 0 := by
    rw [← hE, unitriangularLogarithm_exponential]
  rw [hL]
  rfl

 theorem unitriangularPolynomialBCHCurve_endpoint (A B : StrictUpperTriangular n R) :
    matrixPolynomialEval 1 (unitriangularPolynomialBCHCurve A B) =
      (unitriangularLogarithm (unitriangularExponential A * unitriangularExponential B)).val := by
  simpa only [one_smul] using unitriangularPolynomialBCHCurve_eval A B 1

 theorem unitriangularPolynomialBCHCurve_strict (A B : StrictUpperTriangular n R) :
    MatrixPolynomialDepth 1 (unitriangularPolynomialBCHCurve A B) := by
  apply (matrixPolynomialDepth_iff _ _).mpr
  change MatrixDepth 1 ((matPolyEquiv (R := R)).symm
    (matPolyEquiv (unitriangularLogarithm (unitriangularPolynomialProductCurve A B)).val))
  rw [AlgEquiv.symm_apply_apply]
  exact (unitriangularLogarithm (unitriangularPolynomialProductCurve A B)).property

 theorem unitriangularPolynomialBCHCurve_nilpotent (A B : StrictUpperTriangular n R) :
    (unitriangularPolynomialBCHCurve A B) ^ n = 0 :=
  matrixPolynomialDepth_nilpotent (unitriangularPolynomialBCHCurve_strict A B)

 theorem unitriangularPolynomialProductCurve_matrix_value (A B : StrictUpperTriangular n R) :
    ((unitriangularPolynomialProductCurve A B).val : Matrix (Fin n) (Fin n) (Polynomial R)) =
      matrixFiniteExp (unitriangularPolynomialScale A).val *
        matrixFiniteExp (unitriangularPolynomialScale B).val := rfl

 theorem unitriangularPolynomialScale_exponential_map (A : StrictUpperTriangular n R) :
    matPolyEquiv (matrixFiniteExp (unitriangularPolynomialScale A).val) =
      IsNilpotent.exp (monomial 1 A.val) := by
  rw [matrixFiniteExp_eq_exp (unitriangularPolynomialScale A).property,
    IsNilpotent.map_exp (unitriangularPolynomialScale A).property.nilpotent]
  change IsNilpotent.exp ((matPolyEquiv (R := R))
    ((matPolyEquiv (R := R)).symm (monomial 1 A.val))) = _
  rw [AlgEquiv.apply_symm_apply]

 theorem unitriangularPolynomialBCHCurve_exponential (A B : StrictUpperTriangular n R) :
    IsNilpotent.exp (unitriangularPolynomialBCHCurve A B) =
      IsNilpotent.exp (monomial 1 A.val) * IsNilpotent.exp (monomial 1 B.val) := by
  let g := unitriangularPolynomialProductCurve A B
  let E : Matrix (Fin n) (Fin n) (Polynomial R) ≃ₐ[R]
      Polynomial (Matrix (Fin n) (Fin n) R) := matPolyEquiv
  have he := congrArg E (matrixFiniteExp_logMatrix g)
  change E (matrixFiniteExp (unitriangularLogarithm g).val) = E _ at he
  rw [matrixFiniteExp_eq_exp (unitriangularLogarithm g).property,
    IsNilpotent.map_exp (unitriangularLogarithm g).property.nilpotent] at he
  change IsNilpotent.exp (unitriangularPolynomialBCHCurve A B) =
    E ((unitriangularPolynomialProductCurve A B).val : Matrix (Fin n) (Fin n) (Polynomial R)) at he
  rw [unitriangularPolynomialProductCurve_matrix_value, map_mul] at he
  change IsNilpotent.exp (unitriangularPolynomialBCHCurve A B) =
    matPolyEquiv (matrixFiniteExp (unitriangularPolynomialScale A).val) *
      matPolyEquiv (matrixFiniteExp (unitriangularPolynomialScale B).val) at he
  rw [unitriangularPolynomialScale_exponential_map, unitriangularPolynomialScale_exponential_map] at he
  exact he

 theorem unitriangularPolynomialBCHCurve_right_log_derivative_coeff_mem
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n R)
    (A B : StrictUpperTriangular n R) (hA : A.val ∈ V) (hB : B.val ∈ V) (k : ℕ) :
    ((IsNilpotent.exp (unitriangularPolynomialBCHCurve A B)).derivative *
      (IsNilpotent.exp (-(monomial 1 B.val)) * IsNilpotent.exp (-(monomial 1 A.val)))).coeff k ∈ V := by
  rw [unitriangularPolynomialBCHCurve_exponential,
    polynomial_exp_product_right_log_derivative A.property.nilpotent B.property.nilpotent, coeff_add]
  exact V.add_mem ((polynomialLieSubalgebra_C_mem_iff V _).mpr hA k)
    (polynomial_matrix_exp_conjugation_coeff_mem V hV hA hB 1 k)

end Hindman168
