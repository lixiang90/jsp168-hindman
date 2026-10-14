import Hindman168.RationalMatrixSupport
import Hindman168.UnitriangularExponentialDepth

/-! Rationality of actual Lie-algebra support intersections relative to the
original integer unitriangular lattice. Plain rational matrix coordinates
are identified with that lattice's rational structure only inside the strict
algebra. The genuine subgroup depth intersection is identified by logarithm. -/

noncomputable section
namespace Hindman168
open Matrix Submodule Set

variable {n : ℕ} {R : Type*} [CommRing R]
local instance rationalSupportMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) R) :=
  LieRing.ofAssociativeRing

 theorem rationalMatrixCast_mem_latticeRationalStructure
    {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ (rationalMatrixCastLinear n).range) (hstrict : MatrixDepth 1 X) :
    X ∈ unitriangularLatticeRationalStructure n := by
  obtain ⟨A, hA⟩ := hX
  have hs : MatrixDepth 1 A := by
    intro i j hij
    apply (algebraMap ℚ ℝ).injective
    rw [map_zero]
    have hc : algebraMap ℚ ℝ (A i j) = X i j := congrFun (congrFun hA i) j
    rw [hc]
    exact hstrict i j hij
  exact (unitriangularLatticeRationalStructure_mem_iff X).mpr ⟨⟨A, hs⟩, hA⟩

 theorem rationalUnitriangularLieSubalgebra_iff_matrix
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ) :
    RationalUnitriangularLieSubalgebra V ↔ RationalMatrixSubspace V.toSubmodule := by
  have heq : (V : Set _) ∩ (unitriangularLatticeRationalStructure n : Set (Matrix (Fin n) (Fin n) ℝ)) =
      (V : Set _) ∩ ((rationalMatrixCastLinear n).range : Set (Matrix (Fin n) (Fin n) ℝ)) := by
    ext X
    constructor
    · intro hX
      exact ⟨hX.1, unitriangularLatticeRationalStructure_le_cast_range hX.2⟩
    · intro hX
      exact ⟨hX.1, rationalMatrixCast_mem_latticeRationalStructure hX.2 (hV hX.1)⟩
  unfold RationalUnitriangularLieSubalgebra RationalMatrixSubspace
  rw [heq]
  rfl

 def matrixDepthLieSubalgebra (n k : ℕ) (R : Type*) [CommRing R] :
    LieSubalgebra R (Matrix (Fin n) (Fin n) R) where
  toSubmodule := matrixDepthSubmodule n k R
  lie_mem' hA hB := MatrixDepth.antitone (MatrixDepth.lie hA hB) (by omega)

 theorem matrixDepthLieSubalgebra_mem_iff (k : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    A ∈ matrixDepthLieSubalgebra n k R ↔ MatrixDepth k A := Iff.rfl

 theorem matrixDepthLieSubalgebra_le_strict {k : ℕ} (hk : 1 ≤ k) :
    matrixDepthLieSubalgebra n k R ≤ strictUpperTriangularLieSubalgebra n R := by
  intro A hA
  exact MatrixDepth.antitone hA hk

 theorem rationalUnitriangularLieSubalgebra_depth {k : ℕ} (hk : 1 ≤ k) :
    RationalUnitriangularLieSubalgebra (matrixDepthLieSubalgebra n k ℝ) := by
  rw [rationalUnitriangularLieSubalgebra_iff_matrix _
    (matrixDepthLieSubalgebra_le_strict hk)]
  exact rationalMatrixSubspace_depth k

 theorem rationalUnitriangularLieSubalgebra_inf
    (V W : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (hW : W ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (hrV : RationalUnitriangularLieSubalgebra V)
    (hrW : RationalUnitriangularLieSubalgebra W) :
    RationalUnitriangularLieSubalgebra (V ⊓ W) := by
  rw [rationalUnitriangularLieSubalgebra_iff_matrix _ (inf_le_left.trans hV)]
  exact rationalMatrixSubspace_inf _ _
    ((rationalUnitriangularLieSubalgebra_iff_matrix V hV).mp hrV)
    ((rationalUnitriangularLieSubalgebra_iff_matrix W hW).mp hrW)

 theorem rationalUnitriangularLieSubalgebra_inf_depth
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (hRat : RationalUnitriangularLieSubalgebra V) (k : ℕ) :
    RationalUnitriangularLieSubalgebra (V ⊓ matrixDepthLieSubalgebra n k ℝ) := by
  rw [rationalUnitriangularLieSubalgebra_iff_matrix _ (inf_le_left.trans hV)]
  exact rationalMatrixSubspace_inf _ _
    ((rationalUnitriangularLieSubalgebra_iff_matrix V hV).mp hRat)
    (rationalMatrixSubspace_depth k)

 variable [Algebra ℚ R]

 theorem unitriangularLieSubgroup_inf_depth
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n R) (k : ℕ) :
    unitriangularLieSubgroup (V ⊓ matrixDepthLieSubalgebra n k R) (inf_le_left.trans hV) =
      unitriangularLieSubgroup V hV ⊓ unitriangularDepthSubgroup n k R := by
  ext g
  change ((unitriangularLogarithm g).val ∈ V ∧
      MatrixDepth k (unitriangularLogarithm g).val) ↔
    ((unitriangularLogarithm g).val ∈ V ∧ UnitriangularDepth k g)
  rw [unitriangularLogarithm_depth_iff]

 theorem rationalUnitriangularLieSubalgebra_depth_lattice_log_span
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (hRat : RationalUnitriangularLieSubalgebra V) (k : ℕ) :
    span ℝ (unitriangularLieLatticeLogSet (V ⊓ matrixDepthLieSubalgebra n k ℝ)
      (inf_le_left.trans hV)) = (V ⊓ matrixDepthLieSubalgebra n k ℝ).toSubmodule :=
  rationalUnitriangularLieSubalgebra_lattice_log_span _ (inf_le_left.trans hV)
    (rationalUnitriangularLieSubalgebra_inf_depth V hV hRat k)

end Hindman168
