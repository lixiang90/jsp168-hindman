import Hindman168.UnitriangularDepthCoordinates
import Hindman168.TriangularZeroReduction

/-! Actual generation of every depth subgroup by its allowed transvections,
over arbitrary commutative rings, using exact coordinate elimination. -/

namespace Hindman168
open Matrix

variable {n k : ℕ} {R : Type*} [CommRing R]

 theorem unitriangular_rightTransvection_pivot_ring (g : Unitriangular n R)
    (p : UnitriangularIndex n) (c : R) :
    unitriangularCoordinates
      (g * unitriangularTransvection (unitriangularRow p) (unitriangularColumn p)
        p.property c) p = unitriangularCoordinates g p + c := by
  change ((g.val : Matrix (Fin n) (Fin n) R) *
    Matrix.transvection (unitriangularRow p) (unitriangularColumn p) c)
      (unitriangularRow p) (unitriangularColumn p) = _
  rw [Matrix.mul_transvection_apply_same, g.property.2, mul_one]
  rfl

 theorem unitriangular_rightTransvection_earlier_ring (g : Unitriangular n R)
    (p : UnitriangularIndex n) (c : R) (q : UnitriangularIndex n) (hqp : q < p) :
    unitriangularCoordinates
      (g * unitriangularTransvection (unitriangularRow p) (unitriangularColumn p)
        p.property c) q = unitriangularCoordinates g q := by
  change ((g.val : Matrix (Fin n) (Fin n) R) *
    Matrix.transvection (unitriangularRow p) (unitriangularColumn p) c)
      (unitriangularRow q) (unitriangularColumn q) = _
  by_cases hc : unitriangularColumn q = unitriangularColumn p
  · rw [hc, Matrix.mul_transvection_apply_same]
    rcases (unitriangularIndex_lt_iff q p).mp hqp with hr | ⟨_, hcol⟩
    · rw [g.property.1 hr, mul_zero, add_zero]
      simp only [unitriangularCoordinates, hc]
    · exact False.elim ((ne_of_lt hcol) hc)
  · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hc]
    rfl

 noncomputable def unitriangularDepthTransvectionRing (p : UnitriangularDepthIndex n k) (c : R) :
    unitriangularDepthSubgroup n k R :=
  ⟨unitriangularTransvection (unitriangularRow p.val) (unitriangularColumn p.val)
    p.val.property c, unitriangularDepth_transvection k _ _ p.val.property p.property c⟩

 theorem unitriangularDepth_le_of_transvections (Γ : Subgroup (Unitriangular n R))
    (hΓ : ∀ (i j : Fin n) (hij : i < j), i.val + k ≤ j.val → ∀ c : R,
      unitriangularTransvection i j hij c ∈ Γ) : unitriangularDepthSubgroup n k R ≤ Γ := by
  let L := Γ.comap (unitriangularDepthSubgroup n k R).subtype
  have hL : L = ⊤ := triangularZeroCoordinates_subgroup_eq_top L
    unitriangularDepthCoordinates unitriangularDepthTransvectionRing
    unitriangularDepthCoordinatesEquiv.injective
    (fun p => Matrix.one_apply_ne (ne_of_lt p.val.property))
    (fun p c => hΓ _ _ p.val.property p.property c)
    (fun g p c q hqp => unitriangular_rightTransvection_earlier_ring g.val p.val c q.val hqp)
    (fun g p c => unitriangular_rightTransvection_pivot_ring g.val p.val c)
  intro g hg
  have hmem : (⟨g, hg⟩ : unitriangularDepthSubgroup n k R) ∈ L := by rw [hL]; trivial
  exact hmem

 theorem unitriangularDepth_eq_transvection_closure :
    unitriangularDepthSubgroup n k R = Subgroup.closure
      {u | ∃ (i j : Fin n) (hij : i < j), i.val + k ≤ j.val ∧
        ∃ c : R, unitriangularTransvection i j hij c = u} := by
  apply le_antisymm
  · apply unitriangularDepth_le_of_transvections
    intro i j hij hgap c
    exact Subgroup.subset_closure ⟨i, j, hij, hgap, c, rfl⟩
  · apply (unitriangularDepthSubgroup n k R).closure_le.mpr
    rintro u ⟨i, j, hij, hgap, c, rfl⟩
    exact unitriangularDepth_transvection k i j hij hgap c

end Hindman168
