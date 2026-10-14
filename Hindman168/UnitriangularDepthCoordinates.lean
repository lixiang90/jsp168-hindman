import Hindman168.UnitriangularDepth
import Hindman168.UnitriangularCoordinates
import Mathlib.Topology.Homeomorph.Lemmas

/-! Actual global charts and closedness for each superdiagonal subgroup.
No group lower-central identification is assumed. -/

namespace Hindman168
open Matrix Set Topology

 abbrev UnitriangularDepthIndex (n k : ℕ) :=
  {p : UnitriangularIndex n // (unitriangularRow p).val + k ≤ (unitriangularColumn p).val}

variable {n k : ℕ} {R : Type*} [CommRing R]

 def unitriangularDepthExtend (t : UnitriangularDepthIndex n k → R) :
    UnitriangularIndex n → R := fun p =>
  if h : (unitriangularRow p).val + k ≤ (unitriangularColumn p).val then t ⟨p, h⟩ else 0

 theorem unitriangularDepthExtend_property (t : UnitriangularDepthIndex n k → R) :
    UnitriangularDepth k (unitriangularOfMatrix
      (unitriangularCoordinateMatrix (unitriangularDepthExtend t))
      (unitriangularCoordinateMatrix_property _)) := by
  intro i j hij hgap
  simp [unitriangularCoordinateMatrix, hij, unitriangularDepthExtend,
    unitriangularRow, unitriangularColumn, not_le_of_gt hgap]

 def unitriangularDepthCoordinates (u : unitriangularDepthSubgroup n k R) :
    UnitriangularDepthIndex n k → R := fun p => unitriangularCoordinates u.val p.val

 theorem unitriangularDepthExtend_coordinates (u : unitriangularDepthSubgroup n k R) :
    unitriangularDepthExtend (unitriangularDepthCoordinates u) =
      unitriangularCoordinates u.val := by
  funext p
  by_cases hp : (unitriangularRow p).val + k ≤ (unitriangularColumn p).val
  · simp [unitriangularDepthExtend, hp, unitriangularDepthCoordinates]
  · simp only [unitriangularDepthExtend, dif_neg hp]
    exact (u.property _ _ p.property (lt_of_not_ge hp)).symm

 noncomputable def unitriangularDepthCoordinatesEquiv :
    unitriangularDepthSubgroup n k R ≃ (UnitriangularDepthIndex n k → R) where
  toFun := unitriangularDepthCoordinates
  invFun t := ⟨unitriangularOfMatrix
    (unitriangularCoordinateMatrix (unitriangularDepthExtend t))
    (unitriangularCoordinateMatrix_property _), unitriangularDepthExtend_property t⟩
  left_inv u := by
    apply Subtype.ext
    apply unitriangular_val_injective
    change unitriangularCoordinateMatrix (unitriangularDepthExtend
      (unitriangularDepthCoordinates u)) = (u.val.val : Matrix (Fin n) (Fin n) R)
    rw [unitriangularDepthExtend_coordinates, unitriangularCoordinateMatrix_coordinates]
  right_inv t := by
    funext p
    change unitriangularCoordinateMatrix (unitriangularDepthExtend t)
      (unitriangularRow p.val) (unitriangularColumn p.val) = t p
    rw [unitriangularCoordinateMatrix_entry]
    simp only [unitriangularDepthExtend, dif_pos p.property]

variable [TopologicalSpace R] [IsTopologicalRing R]

 omit [IsTopologicalRing R] in
 theorem unitriangularDepthExtend_continuous :
    Continuous (unitriangularDepthExtend : (UnitriangularDepthIndex n k → R) →
      (UnitriangularIndex n → R)) := by
  apply continuous_pi
  intro p
  by_cases hp : (unitriangularRow p).val + k ≤ (unitriangularColumn p).val
  · simpa only [unitriangularDepthExtend, dif_pos hp] using
      (continuous_apply (⟨p, hp⟩ : UnitriangularDepthIndex n k))
  · simp only [unitriangularDepthExtend, dif_neg hp]
    exact continuous_const

 omit [IsTopologicalRing R] in
 theorem unitriangularDepthCoordinates_continuous :
    Continuous (unitriangularDepthCoordinates : unitriangularDepthSubgroup n k R →
      (UnitriangularDepthIndex n k → R)) := by
  apply continuous_pi
  intro p
  exact (continuous_apply p.val).comp
    (unitriangularCoordinates_continuous.comp continuous_subtype_val)

 theorem unitriangularDepthCoordinates_inverse_continuous :
    Continuous (unitriangularDepthCoordinatesEquiv.symm : (UnitriangularDepthIndex n k → R) →
      unitriangularDepthSubgroup n k R) := by
  have hc := unitriangularCoordinates_inverse_continuous.comp
    (unitriangularDepthExtend_continuous (n := n) (k := k) (R := R))
  exact hc.subtype_mk _

 noncomputable def unitriangularDepthCoordinatesHomeomorph :
    unitriangularDepthSubgroup n k R ≃ₜ (UnitriangularDepthIndex n k → R) where
  toEquiv := unitriangularDepthCoordinatesEquiv
  continuous_toFun := unitriangularDepthCoordinates_continuous
  continuous_invFun := unitriangularDepthCoordinates_inverse_continuous

 omit [IsTopologicalRing R] in
 theorem unitriangularDepth_isClosed [T2Space R] :
    IsClosed (unitriangularDepthSubgroup n k R : Set (Unitriangular n R)) := by
  have heq : (unitriangularDepthSubgroup n k R : Set (Unitriangular n R)) =
      ⋂ (i : Fin n), ⋂ (j : Fin n), ⋂ (_ : i < j), ⋂ (_ : j.val < i.val + k),
        {u | (u.val : Matrix (Fin n) (Fin n) R) i j = 0} := by
    ext u
    simp [unitriangularDepthSubgroup, UnitriangularDepth]
  rw [heq]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _
  apply isClosed_iInter
  intro _
  have hc : Continuous (fun u : Unitriangular n R =>
      (u.val : Matrix (Fin n) (Fin n) R)) :=
    (Units.continuous_val (M := Matrix (Fin n) (Fin n) R)).comp continuous_subtype_val
  exact isClosed_eq (hc.matrix_elem i j) continuous_const

end Hindman168
