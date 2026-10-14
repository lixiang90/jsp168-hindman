import Hindman168.UnitriangularExponentialInverse
import Hindman168.UnitriangularIntegerLattice

/-! Coefficient-ring compatibility of the actual exponential and its inverse.
In particular rational matrices stay rational in both directions. This does
not assert that logarithms of a specified discrete lattice are additive. -/

namespace Hindman168
open Matrix

variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]

 theorem matrixFiniteExp_map (f : R →+* S) (A : Matrix (Fin n) (Fin n) R) :
    f.mapMatrix (matrixFiniteExp A) = matrixFiniteExp (f.mapMatrix A) := by
  simp only [matrixFiniteExp, map_sum, map_rat_smul, map_pow]

 omit [Algebra ℚ R] [Algebra ℚ S] in
 theorem MatrixDepth.map {k : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth k A) (f : R →+* S) : MatrixDepth k (f.mapMatrix A) := by
  intro i j hij
  change f (A i j) = 0
  rw [hA i j hij, map_zero]

 def strictUpperTriangularMap (f : R →+* S) :
    StrictUpperTriangular n R → StrictUpperTriangular n S :=
  fun A => ⟨f.mapMatrix A.val, A.property.map f⟩

 theorem unitriangularLogIteration_map (f : R →+* S) (g : Unitriangular n R) (r : ℕ) :
    f.mapMatrix (unitriangularLogIteration g r) = unitriangularLogIteration (unitriangularMap f g) r := by
  induction r with
  | zero => exact map_zero _
  | succ r ih =>
    simp only [unitriangularLogIteration, map_add, map_sub, matrixFiniteExp_map, ih]
    rfl

 theorem unitriangularLogMatrix_map (f : R →+* S) (g : Unitriangular n R) :
    f.mapMatrix (unitriangularLogMatrix g) = unitriangularLogMatrix (unitriangularMap f g) :=
  unitriangularLogIteration_map f g n

 theorem unitriangularExponential_map (f : R →+* S) (A : StrictUpperTriangular n R) :
    unitriangularMap f (unitriangularExponential A) =
      unitriangularExponential (strictUpperTriangularMap f A) := by
  apply unitriangular_val_injective
  exact matrixFiniteExp_map f A.val

 theorem unitriangularLogarithm_map (f : R →+* S) (g : Unitriangular n R) :
    strictUpperTriangularMap f (unitriangularLogarithm g) =
      unitriangularLogarithm (unitriangularMap f g) := by
  apply Subtype.ext
  exact unitriangularLogMatrix_map f g

 theorem rational_unitriangular_logarithm (g : Unitriangular n ℚ) :
    unitriangularLogarithm (unitriangularMap (algebraMap ℚ ℝ) g) =
      strictUpperTriangularMap (algebraMap ℚ ℝ) (unitriangularLogarithm g) :=
  (unitriangularLogarithm_map _ g).symm

 theorem rational_unitriangular_exponential (A : StrictUpperTriangular n ℚ) :
    unitriangularExponential (strictUpperTriangularMap (algebraMap ℚ ℝ) A) =
      unitriangularMap (algebraMap ℚ ℝ) (unitriangularExponential A) :=
  (unitriangularExponential_map _ A).symm

end Hindman168
