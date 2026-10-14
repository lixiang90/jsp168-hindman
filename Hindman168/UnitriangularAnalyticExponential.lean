import Hindman168.UnitriangularExponentialTopology
import Mathlib.Analysis.Normed.Algebra.Exponential

/-! The finite nilpotent exponential is the actual topological matrix
exponential defined by its infinite power series. The terms beyond the
uniform matrix-dimension cutoff vanish, so no norm or convergence bound is
assumed. This alone does not construct a smooth Lie-group manifold. -/

namespace Hindman168
open Matrix

variable {n : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]
  [TopologicalSpace R] [IsTopologicalRing R]

 theorem matrixFiniteExp_eq_analyticExp {A : Matrix (Fin n) (Fin n) R} (hA : MatrixDepth 1 A) :
    matrixFiniteExp A = NormedSpace.exp A := by
  rw [NormedSpace.exp_eq_tsum_rat]
  unfold matrixFiniteExp
  symm
  apply tsum_eq_sum
  intro r hr
  have hn : n + 2 ≤ r := by simpa only [Finset.mem_range, not_lt] using hr
  have hp : MatrixDepth r (A ^ r) := by simpa only [Nat.one_mul] using hA.pow r
  rw [hp.eq_zero (by omega), smul_zero]

 theorem unitriangularExponential_analytic_value (A : StrictUpperTriangular n R) :
    ((unitriangularExponential A).val : Matrix (Fin n) (Fin n) R) = NormedSpace.exp A.val :=
  matrixFiniteExp_eq_analyticExp A.property

 theorem analyticExp_unitriangular {A : Matrix (Fin n) (Fin n) R} (hA : MatrixDepth 1 A) :
    IsUnitriangular (NormedSpace.exp A) :=
  matrixFiniteExp_eq_analyticExp hA ▸ matrixFiniteExp_unitriangular hA

 theorem analyticExp_logMatrix (g : Unitriangular n R) :
    NormedSpace.exp (unitriangularLogMatrix g) = (g.val : Matrix (Fin n) (Fin n) R) := by
  rw [← matrixFiniteExp_eq_analyticExp (unitriangularLogMatrix_strict g), matrixFiniteExp_logMatrix]

end Hindman168
