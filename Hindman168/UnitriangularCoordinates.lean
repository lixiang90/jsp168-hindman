import Hindman168.UnitriangularGroup
import Mathlib.Data.Prod.Lex
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Group.Units

/-! Global off-diagonal coordinates for the actual unit upper-triangular group.
The order is descending row, then ascending column. The inverse chart is
continuous because the inverse of a determinant-one matrix is its adjugate. -/

namespace Hindman168
open Matrix Set Topology

 abbrev UnitriangularIndex (n : ℕ) :=
  {p : (Fin n)ᵒᵈ ×ₗ Fin n // OrderDual.ofDual (ofLex p).1 < (ofLex p).2}

instance (n : ℕ) : Fintype (UnitriangularIndex n) := inferInstanceAs
  (Fintype {p : (Fin n)ᵒᵈ ×ₗ Fin n // OrderDual.ofDual (ofLex p).1 < (ofLex p).2})
instance (n : ℕ) : LinearOrder (UnitriangularIndex n) := inferInstanceAs
  (LinearOrder {p : (Fin n)ᵒᵈ ×ₗ Fin n // OrderDual.ofDual (ofLex p).1 < (ofLex p).2})

 abbrev unitriangularRow {n : ℕ} (p : UnitriangularIndex n) : Fin n :=
  OrderDual.ofDual (ofLex p.val).1
 abbrev unitriangularColumn {n : ℕ} (p : UnitriangularIndex n) : Fin n :=
  (ofLex p.val).2

 theorem unitriangularIndex_lt_iff {n : ℕ} (p q : UnitriangularIndex n) :
    p < q ↔ unitriangularRow q < unitriangularRow p ∨
      unitriangularRow p = unitriangularRow q ∧
      unitriangularColumn p < unitriangularColumn q := by
  exact Prod.Lex.lt_iff

variable {n : ℕ} {R : Type*} [CommRing R]

 def unitriangularCoordinateMatrix (t : UnitriangularIndex n → R) :
    Matrix (Fin n) (Fin n) R := fun i j =>
  if h : i < j then t ⟨toLex (OrderDual.toDual i, j), h⟩
  else if i = j then 1 else 0

 theorem unitriangularCoordinateMatrix_property (t : UnitriangularIndex n → R) :
    IsUnitriangular (unitriangularCoordinateMatrix t) := by
  refine ⟨?_, ?_⟩
  · intro i j hji
    change j < i at hji
    simp only [unitriangularCoordinateMatrix, dif_neg (not_lt_of_gt hji),
      if_neg (ne_of_gt hji)]
  · intro i
    simp [unitriangularCoordinateMatrix]

 theorem unitriangularCoordinateMatrix_entry (t : UnitriangularIndex n → R)
    (p : UnitriangularIndex n) :
    unitriangularCoordinateMatrix t (unitriangularRow p) (unitriangularColumn p) = t p := by
  unfold unitriangularCoordinateMatrix
  rw [dif_pos p.property]
  rfl

 def unitriangularCoordinates (u : Unitriangular n R) : UnitriangularIndex n → R :=
  fun p => (u.val : Matrix (Fin n) (Fin n) R) (unitriangularRow p) (unitriangularColumn p)

 theorem unitriangularCoordinateMatrix_coordinates (u : Unitriangular n R) :
    unitriangularCoordinateMatrix (unitriangularCoordinates u) =
      (u.val : Matrix (Fin n) (Fin n) R) := by
  ext i j
  by_cases hij : i < j
  · simp [unitriangularCoordinateMatrix, hij, unitriangularCoordinates,
      unitriangularRow, unitriangularColumn]
  · by_cases heq : i = j
    · subst j
      simp [unitriangularCoordinateMatrix, u.property.2]
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm heq)
      simp [unitriangularCoordinateMatrix, hij, heq, u.property.1 hji]

 noncomputable def unitriangularCoordinatesEquiv :
    Unitriangular n R ≃ (UnitriangularIndex n → R) where
  toFun := unitriangularCoordinates
  invFun t := unitriangularOfMatrix (unitriangularCoordinateMatrix t)
    (unitriangularCoordinateMatrix_property t)
  left_inv u := unitriangular_val_injective (unitriangularCoordinateMatrix_coordinates u)
  right_inv t := funext (unitriangularCoordinateMatrix_entry t)

variable [TopologicalSpace R] [IsTopologicalRing R]

 omit [IsTopologicalRing R] in
 theorem unitriangularCoordinateMatrix_continuous :
    Continuous (unitriangularCoordinateMatrix : (UnitriangularIndex n → R) →
      Matrix (Fin n) (Fin n) R) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hij : i < j
  · simpa only [unitriangularCoordinateMatrix, dif_pos hij] using
      (continuous_apply (⟨toLex (OrderDual.toDual i, j), hij⟩ : UnitriangularIndex n))
  · simp only [unitriangularCoordinateMatrix, dif_neg hij]
    exact continuous_const

 omit [IsTopologicalRing R] in
 theorem unitriangularCoordinates_continuous :
    Continuous (unitriangularCoordinates : Unitriangular n R → (UnitriangularIndex n → R)) := by
  apply continuous_pi
  intro p
  have hval : Continuous (fun u : Unitriangular n R =>
      (u.val : Matrix (Fin n) (Fin n) R)) :=
    (Units.continuous_val (M := Matrix (Fin n) (Fin n) R)).comp continuous_subtype_val
  exact hval.matrix_elem (unitriangularRow p) (unitriangularColumn p)

 theorem unitriangularCoordinates_inverse_continuous :
    Continuous (unitriangularCoordinatesEquiv.symm : (UnitriangularIndex n → R) →
      Unitriangular n R) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor
  · exact unitriangularCoordinateMatrix_continuous
  · have heq : (fun t : UnitriangularIndex n → R =>
        (↑(unitriangularCoordinatesEquiv.symm t).val⁻¹ : Matrix (Fin n) (Fin n) R)) =
        fun t => (unitriangularCoordinateMatrix t).adjugate := by
      funext t
      exact unitriangular_inverse_adjugate _
    change Continuous (fun t : UnitriangularIndex n → R =>
      (↑(unitriangularCoordinatesEquiv.symm t).val⁻¹ : Matrix (Fin n) (Fin n) R))
    rw [heq]
    exact unitriangularCoordinateMatrix_continuous.matrix_adjugate

 noncomputable def unitriangularCoordinatesHomeomorph :
    Unitriangular n R ≃ₜ (UnitriangularIndex n → R) where
  toEquiv := unitriangularCoordinatesEquiv
  continuous_toFun := unitriangularCoordinates_continuous
  continuous_invFun := unitriangularCoordinates_inverse_continuous

end Hindman168
