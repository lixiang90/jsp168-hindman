import Hindman168.UnitriangularRationalSupportLayers

/-! Rational support slices suitable for a one-coordinate-at-a-time flag.
Only coordinates no deeper than the first allowed support layer may be
constrained. This hypothesis makes the slice an ideal in the actual strict
matrix Lie algebra, since each ambient bracket raises depth by one. -/

noncomputable section
namespace Hindman168
open Matrix Submodule Set

variable {n : ℕ} {R : Type*} [CommRing R]
local instance rationalSliceMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) R) :=
  LieRing.ofAssociativeRing

 def matrixSupportSliceLieSubalgebra (n k : ℕ) (R : Type*) [CommRing R]
    (hk : 1 ≤ k) (p : Fin n → Fin n → Prop)
    (hp : ∀ i j, p i j → j.val < i.val + k + 1) :
    LieSubalgebra R (Matrix (Fin n) (Fin n) R) where
  toSubmodule := matrixDepthSubmodule n k R ⊓ matrixCoordinateZeroSubmodule n R p
  lie_mem' {A B} hA hB := by
    have hd : MatrixDepth (k + 1) ⁅A, B⁆ :=
      MatrixDepth.antitone (MatrixDepth.lie hA.1 hB.1) (by omega)
    exact ⟨hd.antitone (by omega), fun i j hij => hd i j (hp i j hij)⟩

 theorem matrixSupportSlice_mem_iff (k : ℕ) (hk : 1 ≤ k)
    (p : Fin n → Fin n → Prop) (hp : ∀ i j, p i j → j.val < i.val + k + 1)
    (A : Matrix (Fin n) (Fin n) R) :
    A ∈ matrixSupportSliceLieSubalgebra n k R hk p hp ↔
      MatrixDepth k A ∧ ∀ i j, p i j → A i j = 0 := Iff.rfl

 theorem matrixSupportSlice_le_strict (k : ℕ) (hk : 1 ≤ k)
    (p : Fin n → Fin n → Prop) (hp : ∀ i j, p i j → j.val < i.val + k + 1) :
    matrixSupportSliceLieSubalgebra n k R hk p hp ≤ strictUpperTriangularLieSubalgebra n R := by
  intro A hA
  exact MatrixDepth.antitone hA.1 hk

 theorem matrixSupportSlice_lie_mem_strict (k : ℕ) (hk : 1 ≤ k)
    (p : Fin n → Fin n → Prop) (hp : ∀ i j, p i j → j.val < i.val + k + 1)
    {A B : Matrix (Fin n) (Fin n) R} (hA : MatrixDepth 1 A)
    (hB : B ∈ matrixSupportSliceLieSubalgebra n k R hk p hp) :
    ⁅A, B⁆ ∈ matrixSupportSliceLieSubalgebra n k R hk p hp := by
  have hd : MatrixDepth (k + 1) ⁅A, B⁆ := by
    simpa only [Nat.add_comm 1 k] using MatrixDepth.lie hA hB.1
  exact ⟨hd.antitone (by omega), fun i j hij => hd i j (hp i j hij)⟩

 theorem rationalUnitriangularLieSubalgebra_supportSlice (k : ℕ) (hk : 1 ≤ k)
    (p : Fin n → Fin n → Prop) (hp : ∀ i j, p i j → j.val < i.val + k + 1) :
    RationalUnitriangularLieSubalgebra (matrixSupportSliceLieSubalgebra n k ℝ hk p hp) := by
  rw [rationalUnitriangularLieSubalgebra_iff_matrix _ (matrixSupportSlice_le_strict k hk p hp)]
  exact rationalMatrixSubspace_inf _ _ (rationalMatrixSubspace_depth k)
    (rationalMatrixSubspace_coordinateZero p)

 theorem rationalUnitriangularLieSubalgebra_inf_supportSlice
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (hRat : RationalUnitriangularLieSubalgebra V) (k : ℕ) (hk : 1 ≤ k)
    (p : Fin n → Fin n → Prop) (hp : ∀ i j, p i j → j.val < i.val + k + 1) :
    RationalUnitriangularLieSubalgebra (V ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk p hp) :=
  rationalUnitriangularLieSubalgebra_inf V _ hV (matrixSupportSlice_le_strict k hk p hp)
    hRat (rationalUnitriangularLieSubalgebra_supportSlice k hk p hp)

 theorem rationalUnitriangularLieSubalgebra_supportSlice_lattice_log_span
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (hRat : RationalUnitriangularLieSubalgebra V) (k : ℕ) (hk : 1 ≤ k)
    (p : Fin n → Fin n → Prop) (hp : ∀ i j, p i j → j.val < i.val + k + 1) :
    span ℝ (unitriangularLieLatticeLogSet
      (V ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk p hp) (inf_le_left.trans hV)) =
    (V ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk p hp).toSubmodule :=
  rationalUnitriangularLieSubalgebra_lattice_log_span _ (inf_le_left.trans hV)
    (rationalUnitriangularLieSubalgebra_inf_supportSlice V hV hRat k hk p hp)

 theorem matrixSupportSlice_inf_lie_mem
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n R) (k : ℕ) (hk : 1 ≤ k)
    (p : Fin n → Fin n → Prop) (hp : ∀ i j, p i j → j.val < i.val + k + 1)
    {A B : Matrix (Fin n) (Fin n) R} (hA : A ∈ V)
    (hB : B ∈ V ⊓ matrixSupportSliceLieSubalgebra n k R hk p hp) :
    ⁅A, B⁆ ∈ V ⊓ matrixSupportSliceLieSubalgebra n k R hk p hp :=
  ⟨V.lie_mem hA hB.1, matrixSupportSlice_lie_mem_strict k hk p hp (hV hA) hB.2⟩

end Hindman168
