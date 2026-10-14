import Hindman168.UnitriangularSubalgebraExponent
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! The actual conjugation stabilizer of a matrix Lie subalgebra is a
subgroup. Internal exponentials generate a subgroup contained in this
stabilizer, so every finite product and inverse preserves the Lie subalgebra
and its exponential image. This is not BCH product closure of that image. -/

namespace Hindman168
open Matrix Set

variable {n : ℕ} {R : Type*} [CommRing R]
local instance subalgebraStabilizerMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) R) :=
  LieRing.ofAssociativeRing

 theorem unitriangularConjugationRingHom_one (Y : Matrix (Fin n) (Fin n) R) :
    unitriangularConjugationRingHom (1 : Unitriangular n R) Y = Y := by
  change (1 : ConjAct (Matrix (Fin n) (Fin n) R)ˣ) • Y = Y
  exact one_smul _ Y

 theorem unitriangularConjugationRingHom_mul (g h : Unitriangular n R)
    (Y : Matrix (Fin n) (Fin n) R) :
    unitriangularConjugationRingHom (g * h) Y =
      unitriangularConjugationRingHom g (unitriangularConjugationRingHom h Y) := by
  change (ConjAct.toConjAct g.val * ConjAct.toConjAct h.val) • Y =
    ConjAct.toConjAct g.val • (ConjAct.toConjAct h.val • Y)
  exact mul_smul _ _ _

 theorem unitriangularConjugationRingHom_inv_cancel (g : Unitriangular n R)
    (Y : Matrix (Fin n) (Fin n) R) :
    unitriangularConjugationRingHom g⁻¹ (unitriangularConjugationRingHom g Y) = Y := by
  change (ConjAct.toConjAct g.val)⁻¹ • (ConjAct.toConjAct g.val • Y) = Y
  exact inv_smul_smul _ _

 theorem unitriangularConjugationRingHom_cancel_inv (g : Unitriangular n R)
    (Y : Matrix (Fin n) (Fin n) R) :
    unitriangularConjugationRingHom g (unitriangularConjugationRingHom g⁻¹ Y) = Y := by
  simpa only [inv_inv] using unitriangularConjugationRingHom_inv_cancel g⁻¹ Y

 def unitriangularSubalgebraStabilizer
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R)) : Subgroup (Unitriangular n R) where
  carrier := {g | ∀ Y, unitriangularConjugationRingHom g Y ∈ V ↔ Y ∈ V}
  one_mem' Y := by rw [unitriangularConjugationRingHom_one]
  mul_mem' {g h} hg hh Y := by
    rw [unitriangularConjugationRingHom_mul, hg, hh]
  inv_mem' {g} hg Y := by
    have he := hg (unitriangularConjugationRingHom g⁻¹ Y)
    rw [unitriangularConjugationRingHom_cancel_inv] at he
    exact he.symm

 theorem unitriangularSubalgebraStabilizer_mem_iff
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R)) (g : Unitriangular n R) :
    g ∈ unitriangularSubalgebraStabilizer V ↔
      ∀ Y, unitriangularConjugationRingHom g Y ∈ V ↔ Y ∈ V := Iff.rfl

variable [Algebra ℚ R]

 def unitriangularSubalgebraGenerated
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R)) : Subgroup (Unitriangular n R) :=
  Subgroup.closure (unitriangularSubalgebraExpImage V)

 theorem unitriangularSubalgebraGenerated_le_stabilizer
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n R) :
    unitriangularSubalgebraGenerated V ≤ unitriangularSubalgebraStabilizer V := by
  apply (Subgroup.closure_le (K := unitriangularSubalgebraStabilizer V)).mpr
  intro g hg
  obtain ⟨X, hX, rfl⟩ := (unitriangularSubalgebraExpImage_mem_iff V g).mp hg
  exact unitriangular_subalgebra_exp_conjugation_iff V hV X hX

 theorem unitriangularSubalgebraGenerated_exp_mem
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R))
    (X : StrictUpperTriangular n R) (hX : X.val ∈ V) :
    unitriangularExponential X ∈ unitriangularSubalgebraGenerated V := by
  exact Subgroup.subset_closure
    ((unitriangularSubalgebraExpImage_mem_iff V _).mpr ⟨X, hX, rfl⟩)

 theorem unitriangularSubalgebraGenerated_conjugation_iff
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n R)
    {g : Unitriangular n R} (hg : g ∈ unitriangularSubalgebraGenerated V)
    (Y : Matrix (Fin n) (Fin n) R) :
    unitriangularConjugationRingHom g Y ∈ V ↔ Y ∈ V :=
  unitriangularSubalgebraGenerated_le_stabilizer V hV hg Y

 theorem unitriangularSubalgebraStabilizer_expImage_conjugation_iff
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R))
    {g : Unitriangular n R} (hg : g ∈ unitriangularSubalgebraStabilizer V)
    (u : Unitriangular n R) :
    g * u * g⁻¹ ∈ unitriangularSubalgebraExpImage V ↔ u ∈ unitriangularSubalgebraExpImage V := by
  change (unitriangularLogarithm (g * u * g⁻¹)).val ∈ V ↔ (unitriangularLogarithm u).val ∈ V
  rw [unitriangularLogarithm_conjugation]
  exact hg (unitriangularLogarithm u).val

 theorem unitriangularSubalgebraGenerated_expImage_conjugation_iff
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n R)
    {g : Unitriangular n R} (hg : g ∈ unitriangularSubalgebraGenerated V)
    (u : Unitriangular n R) :
    g * u * g⁻¹ ∈ unitriangularSubalgebraExpImage V ↔ u ∈ unitriangularSubalgebraExpImage V :=
  unitriangularSubalgebraStabilizer_expImage_conjugation_iff V
    (unitriangularSubalgebraGenerated_le_stabilizer V hV hg) u

end Hindman168
