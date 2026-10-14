import Hindman168.UnitriangularSupportConjugation
import Hindman168.UnitriangularBCHLeadingDepth

/-! Genuine lattice pivots and exact coordinate elimination.
A nonzero coordinate on a rational Lie subalgebra has a pivot among the
actual logarithms of its original lattice intersection. Right multiplying
by a real exponential multiple of that pivot kills the coordinate and
preserves the earlier support constraints. Compact fundamental-domain
induction is not assumed in this step. -/

noncomputable section
namespace Hindman168
open Matrix Submodule Set

variable {n : ℕ} {R : Type*} [CommRing R]
local instance supportPivotMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) R) :=
  LieRing.ofAssociativeRing

 def matrixEntryLinearMap (R : Type*) [CommRing R] (i j : Fin n) :
    Matrix (Fin n) (Fin n) R →ₗ[R] R where
  toFun A := A i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem rationalUnitriangularLieSubalgebra_lattice_log_pivot
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (hRat : RationalUnitriangularLieSubalgebra V)
    (i j : Fin n) {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ V) (hij : X i j ≠ 0) :
    ∃ Y ∈ unitriangularLieLatticeLogSet V hV, Y i j ≠ 0 := by
  by_contra hn
  have hzero : ∀ Y ∈ unitriangularLieLatticeLogSet V hV, Y i j = 0 := by
    intro Y hY
    by_contra h
    exact hn ⟨Y, hY, h⟩
  have hle : span ℝ (unitriangularLieLatticeLogSet V hV) ≤
      LinearMap.ker (matrixEntryLinearMap ℝ i j) := by
    apply span_le.mpr
    intro Y hY
    exact hzero Y hY
  have hs := rationalUnitriangularLieSubalgebra_lattice_log_span V hV hRat
  rw [hs] at hle
  exact hij (hle hX)

 theorem rationalUnitriangularLieSubalgebra_original_lattice_pivot
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (hRat : RationalUnitriangularLieSubalgebra V)
    (i j : Fin n) {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ V) (hij : X i j ≠ 0) :
    ∃ γ : Unitriangular n ℝ, γ ∈ unitriangularLieSubgroup V hV ∧
      γ ∈ integerUnitriangularLattice n ∧ (unitriangularLogarithm γ).val i j ≠ 0 := by
  obtain ⟨Y, ⟨γ, hγ, rfl⟩, hY⟩ :=
    rationalUnitriangularLieSubalgebra_lattice_log_pivot V hV hRat i j hX hij
  exact ⟨γ, hγ.1, hγ.2, hY⟩

 theorem unitriangular_log_pivot_elimination (g : Unitriangular n ℝ)
    (Y : StrictUpperTriangular n ℝ) {k : ℕ} (hY : MatrixDepth k Y.val)
    (i j : Fin n) (hij : j.val < i.val + k + 1) (hneq : Y.val i j ≠ 0) :
    (unitriangularLogarithm
      (g * unitriangularExponential (-(((unitriangularLogarithm g).val i j / Y.val i j) • Y)))).val
        i j = 0 := by
  rw [unitriangular_log_right_exponential_layer g _
    ((hY.smul _).neg) i j hij]
  change (unitriangularLogarithm g).val i j +
    -(((unitriangularLogarithm g).val i j / Y.val i j) * Y.val i j) = 0
  rw [div_mul_cancel₀ _ hneq, add_neg_cancel]

 theorem unitriangularSupportSlice_pivot_elimination
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ) (k : ℕ) (hk : 1 ≤ k)
    (p : Fin n → Fin n → Prop) (hp : ∀ i j, p i j → j.val < i.val + k + 1)
    (a b : Fin n) (hab : b.val < a.val + k + 1)
    (Y : StrictUpperTriangular n ℝ)
    (hY : Y.val ∈ V ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk p hp)
    (hneq : Y.val a b ≠ 0) (g : Unitriangular n ℝ)
    (hg : g ∈ unitriangularLieSubgroup (V ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk p hp)
      (inf_le_left.trans hV)) :
    g * unitriangularExponential (-(((unitriangularLogarithm g).val a b / Y.val a b) • Y)) ∈
      unitriangularLieSubgroup (V ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk
        (fun i j => p i j ∨ (i = a ∧ j = b))
        (by intro i j hij; rcases hij with hij | ⟨rfl, rfl⟩; exact hp i j hij; exact hab))
        (inf_le_left.trans hV) := by
  let W := V ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk p hp
  let t := (unitriangularLogarithm g).val a b / Y.val a b
  have hB : (-(t • Y)).val ∈ W := W.neg_mem (W.smul_mem t hY)
  have hE : unitriangularExponential (-(t • Y)) ∈
      unitriangularLieSubgroup W (inf_le_left.trans hV) := by
    change (unitriangularLogarithm (unitriangularExponential (-(t • Y)))).val ∈ W
    rw [unitriangularLogarithm_exponential]
    exact hB
  have hq := (unitriangularLieSubgroup W (inf_le_left.trans hV)).mul_mem hg hE
  have hzero := unitriangular_log_pivot_elimination g Y hY.2.1 a b hab hneq
  change (unitriangularLogarithm (g * unitriangularExponential (-(t • Y)))).val ∈ V ∧
    MatrixDepth k (unitriangularLogarithm (g * unitriangularExponential (-(t • Y)))).val ∧
    ∀ i j, p i j ∨ (i = a ∧ j = b) →
      (unitriangularLogarithm (g * unitriangularExponential (-(t • Y)))).val i j = 0
  refine ⟨hq.1, hq.2.1, ?_⟩
  intro i j hij
  rcases hij with hij | ⟨rfl, rfl⟩
  · exact hq.2.2 i j hij
  · exact hzero

end Hindman168
