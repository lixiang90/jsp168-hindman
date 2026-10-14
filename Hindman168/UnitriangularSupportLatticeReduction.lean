import Hindman168.UnitriangularOneParameterLattice

/-! One genuine noncommutative lattice-reduction step. A lattice pivot
eliminates the next coordinate. Splitting its parameter into a unit-interval
remainder and an integer, and conjugating the residual into the next normal
support slice, gives a bounded left factor and an actual original lattice
right factor. This is a step of a compact fundamental-domain induction,
not a claim that the full induction or arbitrary Lie-group transfer is done. -/

noncomputable section
namespace Hindman168
open Matrix Set

variable {n : ℕ}
local instance supportReductionMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) ℝ) :=
  LieRing.ofAssociativeRing

 theorem unitriangularSupportSlice_lattice_reduction_step
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ) (k : ℕ) (hk : 1 ≤ k)
    (p : Fin n → Fin n → Prop) (hp : ∀ i j, p i j → j.val < i.val + k + 1)
    (a b : Fin n) (hab : b.val < a.val + k + 1) (γ : Unitriangular n ℝ)
    (hγ : γ ∈ unitriangularLieSubgroup (V ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk p hp)
      (inf_le_left.trans hV))
    (hγZ : γ ∈ integerUnitriangularLattice n)
    (hneq : (unitriangularLogarithm γ).val a b ≠ 0) (g : Unitriangular n ℝ)
    (hg : g ∈ unitriangularLieSubgroup (V ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk p hp)
      (inf_le_left.trans hV)) :
    ∃ r ∈ Icc (0 : ℝ) 1, ∃ u ∈
      unitriangularLieSubgroup (V ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk
        (fun i j => p i j ∨ (i = a ∧ j = b))
        (by intro i j hij; rcases hij with hij | ⟨rfl, rfl⟩; exact hp i j hij; exact hab))
        (inf_le_left.trans hV),
      ∃ z : ℤ, γ ^ z ∈ integerUnitriangularLattice n ∧
        g = unitriangularExponential (r • unitriangularLogarithm γ) * u * γ ^ z := by
  let Y := unitriangularLogarithm γ
  let t := (unitriangularLogarithm g).val a b / Y.val a b
  let z : ℤ := Int.floor t
  let r : ℝ := t - (z : ℝ)
  let q := g * unitriangularExponential (-(t • Y))
  let c := unitriangularExponential (-(r • Y))
  let u := c * q * c⁻¹
  let p' : Fin n → Fin n → Prop := fun i j => p i j ∨ (i = a ∧ j = b)
  have hp' : ∀ i j, p' i j → j.val < i.val + k + 1 := by
    intro i j hij
    rcases hij with hij | ⟨rfl, rfl⟩
    · exact hp i j hij
    · exact hab
  have hq : q ∈ unitriangularLieSubgroup
      (V ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk p' hp') (inf_le_left.trans hV) :=
    unitriangularSupportSlice_pivot_elimination V hV k hk p hp a b hab Y hγ hneq g hg
  have hc : c ∈ unitriangularLieSubgroup V hV := by
    change (unitriangularLogarithm (unitriangularExponential (-(r • Y)))).val ∈ V
    rw [unitriangularLogarithm_exponential]
    exact V.neg_mem (V.smul_mem r hγ.1)
  have hu : u ∈ unitriangularLieSubgroup
      (V ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk p' hp') (inf_le_left.trans hV) :=
    unitriangularSupportSlice_inf_conjugation_mem V hV k hk p' hp' hc hq
  have hr : r ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (Int.floor_le t)
    · have ht := Int.lt_floor_add_one t
      change t - (Int.floor t : ℝ) ≤ 1
      linarith
  have hz : γ ^ z = unitriangularExponential ((z : ℝ) • Y) := by
    rw [unitriangularExponential_int_smul]
    dsimp [Y]
    rw [unitriangularExponential_logarithm]
  have ht : r + (z : ℝ) = t := by dsimp [r]; ring
  refine ⟨r, hr, u, hu, z, (integerUnitriangularLattice n).zpow_mem hγZ z, ?_⟩
  symm
  calc
    unitriangularExponential (r • Y) * u * γ ^ z =
        q * (unitriangularExponential (r • Y) * unitriangularExponential ((z : ℝ) • Y)) := by
      dsimp [u, c]
      rw [hz, unitriangularExponential_neg]
      group
    _ = q * unitriangularExponential (t • Y) := by
      rw [← unitriangularExponential_smul_add, ht]
    _ = g := by
      dsimp [q]
      rw [unitriangularExponential_neg]
      group

end Hindman168
