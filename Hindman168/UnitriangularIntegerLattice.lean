import Hindman168.UnitriangularCoordinates
import Hindman168.TriangularGroupReduction
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-! Integer matrices give an actual discrete subgroup of the real
unit upper-triangular group. Right transvections satisfy the ordered triangular
laws, yielding a compact natural coset space in every finite dimension. -/

namespace Hindman168
open Matrix Set Topology

variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

 def unitriangularMap (f : R →+* S) : Unitriangular n R →* Unitriangular n S where
  toFun u := ⟨Matrix.GeneralLinearGroup.map f u.val, by
    refine ⟨?_, ?_⟩
    · intro i j hji
      change f ((u.val : Matrix (Fin n) (Fin n) R) i j) = 0
      rw [u.property.1 hji, map_zero]
    · intro i
      change f ((u.val : Matrix (Fin n) (Fin n) R) i i) = 1
      rw [u.property.2, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.val v.val)

 theorem unitriangularMap_entry (f : R →+* S) (u : Unitriangular n R) (i j : Fin n) :
    ((unitriangularMap f u).val : Matrix (Fin n) (Fin n) S) i j =
      f ((u.val : Matrix (Fin n) (Fin n) R) i j) := rfl

 theorem unitriangularMap_transvection (f : R →+* S) (i j : Fin n)
    (hij : i < j) (c : R) :
    unitriangularMap f (unitriangularTransvection i j hij c) =
      unitriangularTransvection i j hij (f c) := by
  apply unitriangular_val_injective
  ext a b
  change f (Matrix.transvection i j c a b) = Matrix.transvection i j (f c) a b
  simp only [Matrix.transvection, Matrix.add_apply, map_add, Matrix.single, Matrix.of_apply]
  split_ifs <;> simp [Matrix.one_apply]

 def integerUnitriangularLattice (n : ℕ) : Subgroup (Unitriangular n ℝ) :=
  (unitriangularMap (n := n) (Int.castRingHom ℝ)).range

 theorem integerUnitriangularLattice_entry {g : Unitriangular n ℝ}
    (hg : g ∈ integerUnitriangularLattice n) (i j : Fin n) :
    ∃ z : ℤ, (g.val : Matrix (Fin n) (Fin n) ℝ) i j = z := by
  obtain ⟨u, rfl⟩ := hg
  exact ⟨(u.val : Matrix (Fin n) (Fin n) ℤ) i j, rfl⟩

 theorem integerUnitriangularLattice_mem_iff_coordinates (g : Unitriangular n ℝ) :
    g ∈ integerUnitriangularLattice n ↔
      ∀ p, ∃ z : ℤ, unitriangularCoordinates g p = z := by
  classical
  constructor
  · intro hg p
    exact integerUnitriangularLattice_entry hg _ _
  · intro hg
    choose t ht using hg
    let u : Unitriangular n ℤ := unitriangularCoordinatesEquiv.symm t
    refine ⟨u, ?_⟩
    apply unitriangularCoordinatesEquiv.injective
    funext p
    change ((u.val : Matrix (Fin n) (Fin n) ℤ) (unitriangularRow p)
      (unitriangularColumn p) : ℝ) = unitriangularCoordinates g p
    have hu : (u.val : Matrix (Fin n) (Fin n) ℤ) (unitriangularRow p)
        (unitriangularColumn p) = t p :=
      congrFun (unitriangularCoordinatesEquiv.apply_symm_apply t) p
    rw [hu]
    exact (ht p).symm

 theorem integerUnitriangularLattice_transvection (p : UnitriangularIndex n) (z : ℤ) :
    unitriangularTransvection (unitriangularRow p) (unitriangularColumn p) p.property
      (z : ℝ) ∈ integerUnitriangularLattice n := by
  refine ⟨unitriangularTransvection (unitriangularRow p) (unitriangularColumn p)
    p.property z, ?_⟩
  exact unitriangularMap_transvection (Int.castRingHom ℝ) _ _ _ z

 theorem unitriangular_rightTransvection_pivot (g : Unitriangular n ℝ)
    (p : UnitriangularIndex n) (z : ℤ) :
    unitriangularCoordinates
      (g * unitriangularTransvection (unitriangularRow p) (unitriangularColumn p)
        p.property (z : ℝ)) p = unitriangularCoordinates g p + (z : ℝ) := by
  change ((g.val : Matrix (Fin n) (Fin n) ℝ) *
    Matrix.transvection (unitriangularRow p) (unitriangularColumn p) (z : ℝ))
      (unitriangularRow p) (unitriangularColumn p) = _
  rw [Matrix.mul_transvection_apply_same, g.property.2, mul_one]
  rfl

 theorem unitriangular_rightTransvection_earlier (g : Unitriangular n ℝ)
    (p : UnitriangularIndex n) (z : ℤ) (q : UnitriangularIndex n) (hqp : q < p) :
    unitriangularCoordinates
      (g * unitriangularTransvection (unitriangularRow p) (unitriangularColumn p)
        p.property (z : ℝ)) q = unitriangularCoordinates g q := by
  change ((g.val : Matrix (Fin n) (Fin n) ℝ) *
    Matrix.transvection (unitriangularRow p) (unitriangularColumn p) (z : ℝ))
      (unitriangularRow q) (unitriangularColumn q) = _
  by_cases hc : unitriangularColumn q = unitriangularColumn p
  · rw [hc, Matrix.mul_transvection_apply_same]
    rcases (unitriangularIndex_lt_iff q p).mp hqp with hr | ⟨_, hcol⟩
    · rw [g.property.1 hr, mul_zero, add_zero]
      simp only [unitriangularCoordinates, hc]
    · exact False.elim ((ne_of_lt hcol) hc)
  · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hc]
    rfl

 theorem integerUnitriangularLattice_representatives (g : Unitriangular n ℝ) :
    ∃ x γ, γ ∈ integerUnitriangularLattice n ∧ g = x * γ ∧
      ∀ p, unitriangularCoordinates x p ∈ Ico 0 1 := by
  exact triangularCoordinates_ordered_reduction (integerUnitriangularLattice n)
    unitriangularCoordinates
    (fun p z => unitriangularTransvection (unitriangularRow p) (unitriangularColumn p)
      p.property (z : ℝ)) integerUnitriangularLattice_transvection
    unitriangular_rightTransvection_earlier unitriangular_rightTransvection_pivot g

 theorem integerUnitriangularLattice_quotient_compact :
    CompactSpace (Unitriangular n ℝ ⧸ integerUnitriangularLattice n) := by
  exact triangularCoordinates_compact_quotient (integerUnitriangularLattice n)
    unitriangularCoordinatesHomeomorph
    (fun p z => unitriangularTransvection (unitriangularRow p) (unitriangularColumn p)
      p.property (z : ℝ)) integerUnitriangularLattice_transvection
    unitriangular_rightTransvection_earlier unitriangular_rightTransvection_pivot

 theorem integerUnitriangularLattice_discrete :
    DiscreteTopology (integerUnitriangularLattice n) := by
  let c : integerUnitriangularLattice n → (UnitriangularIndex n → ℝ) :=
    fun g => unitriangularCoordinates g.val
  have hc : Continuous c := unitriangularCoordinates_continuous.comp continuous_subtype_val
  let C : Set (UnitriangularIndex n → ℝ) := pi univ (fun _ => Ioo (-1 / 2) (1 / 2))
  have hC : IsOpen C := isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)
  have heq : c ⁻¹' C = {1} := by
    ext g
    constructor
    · intro hg
      apply mem_singleton_iff.mpr
      apply Subtype.ext
      apply unitriangularCoordinatesEquiv.injective
      funext p
      have hbound := mem_pi.mp hg p (mem_univ p)
      obtain ⟨z, hz⟩ := integerUnitriangularLattice_entry g.property
        (unitriangularRow p) (unitriangularColumn p)
      have hval : c g p = (z : ℝ) := hz
      rw [hval] at hbound
      have hlo : (-1 : ℤ) < z := by exact_mod_cast (by linarith [hbound.1] : (-1 : ℝ) < z)
      have hhi : z < (1 : ℤ) := by exact_mod_cast (by linarith [hbound.2] : (z : ℝ) < 1)
      have hz0 : z = 0 := by omega
      change c g p = (1 : Matrix (Fin n) (Fin n) ℝ) (unitriangularRow p)
        (unitriangularColumn p)
      rw [hval, hz0, Int.cast_zero, Matrix.one_apply_ne (ne_of_lt p.property)]
    · intro hg
      subst g
      apply mem_pi.mpr
      intro p _
      change (1 : Matrix (Fin n) (Fin n) ℝ) (unitriangularRow p)
        (unitriangularColumn p) ∈ Ioo (-1 / 2) (1 / 2)
      rw [Matrix.one_apply_ne (ne_of_lt p.property)]
      norm_num
  exact discreteTopology_of_isOpen_singleton_one (heq ▸ hC.preimage hc)

end Hindman168
