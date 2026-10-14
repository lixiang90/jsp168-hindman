import Hindman168.UnitriangularRationalSupportPivot
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Order.Floor.Ring

/-! The actual exponential along one strict real matrix is an additive-to-
group homomorphism. Integer parameters are genuine powers of its value at
one, so a chosen original lattice pivot has genuine integer periods.
Only this single direction is used; no additive lattice of all logarithms
is asserted. Its unit parameter segment is compact in the natural topology. -/

noncomputable section
namespace Hindman168
open Matrix Set

variable {n : ℕ}

 theorem unitriangularExponential_smul_add (Y : StrictUpperTriangular n ℝ) (r s : ℝ) :
    unitriangularExponential ((r + s) • Y) =
      unitriangularExponential (r • Y) * unitriangularExponential (s • Y) := by
  rw [add_smul]
  apply unitriangularExponential_add_of_commute
  change (r • Y.val) * (s • Y.val) = (s • Y.val) * (r • Y.val)
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_comm r s]

 def unitriangularOneParameter (Y : StrictUpperTriangular n ℝ) :
    ℝ →+ Additive (Unitriangular n ℝ) where
  toFun t := Additive.ofMul (unitriangularExponential (t • Y))
  map_zero' := by
    change unitriangularExponential ((0 : ℝ) • Y) = 1
    rw [zero_smul]
    apply unitriangular_val_injective
    exact matrixFiniteExp_zero
  map_add' r s := unitriangularExponential_smul_add Y r s

 theorem unitriangularExponential_int_smul (Y : StrictUpperTriangular n ℝ) (z : ℤ) :
    unitriangularExponential ((z : ℝ) • Y) = (unitriangularExponential Y) ^ z := by
  have h := congrArg Additive.toMul (map_zsmul (unitriangularOneParameter Y) z (1 : ℝ))
  change unitriangularExponential ((z • (1 : ℝ)) • Y) =
    (unitriangularExponential ((1 : ℝ) • Y)) ^ z at h
  simpa only [zsmul_eq_mul, mul_one, one_smul] using h

 theorem unitriangular_lattice_log_integer_period (γ : Unitriangular n ℝ)
    (hγ : γ ∈ integerUnitriangularLattice n) (z : ℤ) :
    unitriangularExponential ((z : ℝ) • unitriangularLogarithm γ) ∈
      integerUnitriangularLattice n := by
  rw [unitriangularExponential_int_smul, unitriangularExponential_logarithm]
  exact (integerUnitriangularLattice n).zpow_mem hγ z

 theorem unitriangularOneParameter_segment_isCompact (Y : StrictUpperTriangular n ℝ) :
    IsCompact ((fun t : ℝ => unitriangularExponential (t • Y)) '' Icc 0 1) := by
  exact isCompact_Icc.image (unitriangularExponential_continuous.comp
    (continuous_id.smul continuous_const))

 theorem unitriangular_lattice_one_parameter_reduction (Y : StrictUpperTriangular n ℝ)
    (hY : unitriangularExponential Y ∈ integerUnitriangularLattice n) (t : ℝ) :
    ∃ a ∈ Icc (0 : ℝ) 1, ∃ γ ∈ integerUnitriangularLattice n,
      unitriangularExponential (t • Y) = unitriangularExponential (a • Y) * γ := by
  let z : ℤ := Int.floor t
  let a : ℝ := t - (z : ℝ)
  have ha : a ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (Int.floor_le t)
    · have h := Int.lt_floor_add_one t
      change t - (Int.floor t : ℝ) ≤ 1
      linarith
  refine ⟨a, ha, unitriangularExponential ((z : ℝ) • Y), ?_, ?_⟩
  · rw [unitriangularExponential_int_smul]
    exact (integerUnitriangularLattice n).zpow_mem hY z
  · rw [← unitriangularExponential_smul_add]
    congr 2
    dsimp [a]
    ring

end Hindman168
