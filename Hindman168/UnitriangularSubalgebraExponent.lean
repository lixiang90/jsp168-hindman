import Hindman168.NilpotentLieSubalgebraConjugation
import Hindman168.UnitriangularExponentialConjugation

/-! Arbitrary Lie subalgebras of the strict matrix algebra are invariant
under internal exponential conjugation. No claim that their exponential
image is already closed under arbitrary products is made here. -/

namespace Hindman168
open Matrix Set

variable {n : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]
local instance subalgebraExponentMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) R) :=
  LieRing.ofAssociativeRing

 theorem unitriangular_exponential_inverse_value (X : StrictUpperTriangular n R) :
    (↑(unitriangularExponential X).val⁻¹ : Matrix (Fin n) (Fin n) R) = IsNilpotent.exp (-X.val) := by
  change (((unitriangularExponential X)⁻¹).val : Matrix (Fin n) (Fin n) R) = _
  rw [← unitriangularExponential_neg, unitriangularExponential_value]
  rfl

 theorem unitriangular_subalgebra_exp_conjugation_iff
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n R)
    (X : StrictUpperTriangular n R) (hX : X.val ∈ V) (Y : Matrix (Fin n) (Fin n) R) :
    unitriangularConjugationRingHom (unitriangularExponential X) Y ∈ V ↔ Y ∈ V := by
  rw [unitriangularConjugationRingHom_apply, unitriangularExponential_value,
    unitriangular_exponential_inverse_value]
  exact lieSubalgebra_nilpotent_exp_conjugation_iff V hX (hV hX).nilpotent Y

 theorem unitriangular_subalgebra_exp_conjugation_mem
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n R)
    (X : StrictUpperTriangular n R) (hX : X.val ∈ V)
    {Y : Matrix (Fin n) (Fin n) R} (hY : Y ∈ V) :
    unitriangularConjugationRingHom (unitriangularExponential X) Y ∈ V :=
  (unitriangular_subalgebra_exp_conjugation_iff V hV X hX Y).mpr hY

 def unitriangularSubalgebraExpImage (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R)) :
    Set (Unitriangular n R) := {g | (unitriangularLogarithm g).val ∈ V}

 theorem unitriangularSubalgebraExpImage_mem_iff
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R)) (g : Unitriangular n R) :
    g ∈ unitriangularSubalgebraExpImage V ↔
      ∃ X : StrictUpperTriangular n R, X.val ∈ V ∧ unitriangularExponential X = g := by
  constructor
  · intro hg
    exact ⟨unitriangularLogarithm g, hg, unitriangularExponential_logarithm g⟩
  · rintro ⟨X, hX, rfl⟩
    change (unitriangularLogarithm (unitriangularExponential X)).val ∈ V
    rw [unitriangularLogarithm_exponential]
    exact hX

 theorem unitriangularSubalgebraExpImage_conjugation_iff
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n R)
    (X : StrictUpperTriangular n R) (hX : X.val ∈ V) (g : Unitriangular n R) :
    unitriangularExponential X * g * (unitriangularExponential X)⁻¹ ∈
      unitriangularSubalgebraExpImage V ↔ g ∈ unitriangularSubalgebraExpImage V := by
  change (unitriangularLogarithm
    (unitriangularExponential X * g * (unitriangularExponential X)⁻¹)).val ∈ V ↔
      (unitriangularLogarithm g).val ∈ V
  rw [unitriangularLogarithm_conjugation]
  exact unitriangular_subalgebra_exp_conjugation_iff V hV X hX (unitriangularLogarithm g).val

 theorem unitriangularSubalgebraExpImage_inverse_iff
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R)) (g : Unitriangular n R) :
    g⁻¹ ∈ unitriangularSubalgebraExpImage V ↔ g ∈ unitriangularSubalgebraExpImage V := by
  have heq : unitriangularLogarithm g⁻¹ = -unitriangularLogarithm g := by
    apply unitriangularExponentialEquiv.injective
    change unitriangularExponential (unitriangularLogarithm g⁻¹) =
      unitriangularExponential (-unitriangularLogarithm g)
    rw [unitriangularExponential_logarithm, unitriangularExponential_neg,
      unitriangularExponential_logarithm]
  change (unitriangularLogarithm g⁻¹).val ∈ V ↔ (unitriangularLogarithm g).val ∈ V
  rw [heq]
  exact V.neg_mem_iff

end Hindman168
