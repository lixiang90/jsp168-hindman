import Hindman168.UnitriangularLieConjugation

/-! Exponential/logarithm intertwine actual group conjugation and the
constructed matrix Lie conjugation. Rational coefficient preimages are
preserved, including logarithms of conjugates of the original integer
lattice. This does not assert lattice invariance under rational conjugation
or a theorem for arbitrary rational Lie subgroups. -/

namespace Hindman168
open Matrix

variable {n : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]
local instance exponentialConjugationMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) R) :=
  LieRing.ofAssociativeRing

 theorem unitriangularExponential_conjugation (g : Unitriangular n R)
    (A : UnitriangularLieAlgebra n R) :
    unitriangularExponential (unitriangularConjugationLieHom g A) =
      g * unitriangularExponential A * g⁻¹ := by
  apply unitriangular_val_injective
  change matrixFiniteExp (unitriangularConjugationRingHom g A.val) =
    (g.val : Matrix (Fin n) (Fin n) R) * matrixFiniteExp A.val *
      (↑g.val⁻¹ : Matrix (Fin n) (Fin n) R)
  rw [matrixFiniteExp_eq_exp (A.property.unitriangular_conjugate g), matrixFiniteExp_eq_exp A.property]
  exact (IsNilpotent.map_exp A.property.nilpotent (unitriangularConjugationRingHom g)).symm

 theorem unitriangularLogarithm_conjugation (g u : Unitriangular n R) :
    unitriangularLogarithm (g * u * g⁻¹) =
      unitriangularConjugationLieHom g (unitriangularLogarithm u) := by
  apply unitriangularExponentialEquiv.injective
  change unitriangularExponential (unitriangularLogarithm (g * u * g⁻¹)) =
    unitriangularExponential (unitriangularConjugationLieHom g (unitriangularLogarithm u))
  rw [unitriangularExponential_logarithm, unitriangularExponential_conjugation,
    unitriangularExponential_logarithm]

variable {S : Type*} [CommRing S] [Algebra ℚ S]

 omit [Algebra ℚ R] [Algebra ℚ S] in
 theorem unitriangularConjugationLie_map (f : R →+* S) (g : Unitriangular n R)
    (A : UnitriangularLieAlgebra n R) :
    unitriangularConjugationLieHom (unitriangularMap f g) (strictUpperTriangularMap f A) =
      strictUpperTriangularMap f (unitriangularConjugationLieHom g A) := by
  apply Subtype.ext
  change f.mapMatrix (g.val : Matrix (Fin n) (Fin n) R) * f.mapMatrix A.val *
      f.mapMatrix (↑g.val⁻¹ : Matrix (Fin n) (Fin n) R) =
    f.mapMatrix ((g.val : Matrix (Fin n) (Fin n) R) * A.val *
      (↑g.val⁻¹ : Matrix (Fin n) (Fin n) R))
  rw [map_mul, map_mul]

 theorem unitriangular_rational_conjugation (g : Unitriangular n ℝ)
    (A : UnitriangularLieAlgebra n ℝ)
    (hg : ∃ u : Unitriangular n ℚ, unitriangularMap (algebraMap ℚ ℝ) u = g)
    (hA : ∃ B : StrictUpperTriangular n ℚ, strictUpperTriangularMap (algebraMap ℚ ℝ) B = A) :
    ∃ B : StrictUpperTriangular n ℚ,
      strictUpperTriangularMap (algebraMap ℚ ℝ) B = unitriangularConjugationLieHom g A := by
  obtain ⟨u, rfl⟩ := hg
  obtain ⟨B, rfl⟩ := hA
  exact ⟨unitriangularConjugationLieHom u B, (unitriangularConjugationLie_map _ u B).symm⟩

 theorem integerUnitriangularLattice_rational_conjugate_log (g γ : Unitriangular n ℝ)
    (hg : ∃ u : Unitriangular n ℚ, unitriangularMap (algebraMap ℚ ℝ) u = g)
    (hγ : γ ∈ integerUnitriangularLattice n) :
    ∃ B : StrictUpperTriangular n ℚ,
      strictUpperTriangularMap (algebraMap ℚ ℝ) B = unitriangularLogarithm (g * γ * g⁻¹) := by
  rw [unitriangularLogarithm_conjugation]
  exact unitriangular_rational_conjugation g (unitriangularLogarithm γ) hg
    (integerUnitriangularLattice_log_rational γ hγ)

end Hindman168
