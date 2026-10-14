import Hindman168.UnitriangularInvariantField
import Hindman168.UnitriangularLieLowerCentral

/-! The native tangent Lie algebra of the original real unitriangular group
is identified with its actual strict matrix Lie algebra. The bracket proof
uses the computed native invariant fields, not a supplied bracket identity. -/

namespace Hindman168
open Matrix
open scoped Manifold ContDiff Matrix.Norms.Elementwise

local instance matrixNativeComparisonLieRing (n : ℕ) :
    LieRing (Matrix (Fin n) (Fin n) ℝ) := LieRing.ofAssociativeRing

variable {n : ℕ}

 theorem unitriangular_native_bracket_matrix
    (v w : GroupLieAlgebra 𝓘(ℝ, UnitriangularIndex n → ℝ) (Unitriangular n ℝ)) :
    unitriangularTangentMatrix n
        (⁅v, w⁆ : GroupLieAlgebra 𝓘(ℝ, UnitriangularIndex n → ℝ) (Unitriangular n ℝ)) =
      unitriangularTangentMatrix n v * unitriangularTangentMatrix n w -
        unitriangularTangentMatrix n w * unitriangularTangentMatrix n v := by
  rw [unitriangular_native_bracket_coordinates]
  apply unitriangularTangentMatrix_offDiagonal
  exact ((unitriangularTangentMatrix_strict v).mul (unitriangularTangentMatrix_strict w)).sub
    ((unitriangularTangentMatrix_strict w).mul (unitriangularTangentMatrix_strict v)) |>.antitone
      (by omega)

 noncomputable def unitriangularNativeLieEquiv (n : ℕ) :
    GroupLieAlgebra 𝓘(ℝ, UnitriangularIndex n → ℝ) (Unitriangular n ℝ) ≃ₗ⁅ℝ⁆
      UnitriangularLieAlgebra n ℝ where
  toFun v := ⟨unitriangularTangentMatrix n v, unitriangularTangentMatrix_strict v⟩
  invFun X := matrixOffDiagonalCoordinates n X.val
  left_inv v := matrixOffDiagonalCoordinates_tangentMatrix v
  right_inv X := by
    apply Subtype.ext
    exact unitriangularTangentMatrix_offDiagonal X.property
  map_add' v w := by
    apply Subtype.ext
    exact (unitriangularTangentMatrix n).map_add v w
  map_smul' c v := by
    apply Subtype.ext
    exact (unitriangularTangentMatrix n).map_smul c v
  map_lie' {v w} := by
    apply Subtype.ext
    exact unitriangular_native_bracket_matrix v w

 theorem unitriangularNativeLieEquiv_value
    (v : GroupLieAlgebra 𝓘(ℝ, UnitriangularIndex n → ℝ) (Unitriangular n ℝ)) :
    (unitriangularNativeLieEquiv n v).val = unitriangularTangentMatrix n v := rfl

 theorem unitriangularNativeLieEquiv_inverse (X : UnitriangularLieAlgebra n ℝ) :
    (unitriangularNativeLieEquiv n).symm X = matrixOffDiagonalCoordinates n X.val := rfl

 theorem unitriangularNativeLieEquiv_bracket
    (v w : GroupLieAlgebra 𝓘(ℝ, UnitriangularIndex n → ℝ) (Unitriangular n ℝ)) :
    unitriangularNativeLieEquiv n ⁅v, w⁆ =
      ⁅unitriangularNativeLieEquiv n v, unitriangularNativeLieEquiv n w⁆ :=
  (unitriangularNativeLieEquiv n).map_lie v w

 theorem unitriangularNativeLie_lowerCentral_map (k : ℕ) :
    LieIdeal.map (unitriangularNativeLieEquiv n).toLieHom
      (LieModule.lowerCentralSeries ℝ
        (GroupLieAlgebra 𝓘(ℝ, UnitriangularIndex n → ℝ) (Unitriangular n ℝ))
        (GroupLieAlgebra 𝓘(ℝ, UnitriangularIndex n → ℝ) (Unitriangular n ℝ)) k) =
      unitriangularLieDepth n (k + 1) ℝ := by
  rw [LieIdeal.lowerCentralSeries_map_eq k (unitriangularNativeLieEquiv n).surjective,
    unitriangularLie_lowerCentral_eq_depth]

 theorem unitriangularNativeLie_lowerCentral_terminal :
    LieModule.lowerCentralSeries ℝ
      (GroupLieAlgebra 𝓘(ℝ, UnitriangularIndex n → ℝ) (Unitriangular n ℝ))
      (GroupLieAlgebra 𝓘(ℝ, UnitriangularIndex n → ℝ) (Unitriangular n ℝ)) (n - 1) = ⊥ := by
  apply LieIdeal.bot_of_map_eq_bot (unitriangularNativeLieEquiv n).injective
  rw [unitriangularNativeLie_lowerCentral_map]
  exact unitriangularLieDepth_terminal (by omega)

 theorem unitriangularNativeLie_isNilpotent :
    LieModule.IsNilpotent
      (GroupLieAlgebra 𝓘(ℝ, UnitriangularIndex n → ℝ) (Unitriangular n ℝ))
      (GroupLieAlgebra 𝓘(ℝ, UnitriangularIndex n → ℝ) (Unitriangular n ℝ)) :=
  LieModule.IsNilpotent.mk _ unitriangularNativeLie_lowerCentral_terminal

 instance unitriangularNativeLieModuleIsNilpotent (n : ℕ) :
    LieModule.IsNilpotent
      (GroupLieAlgebra 𝓘(ℝ, UnitriangularIndex n → ℝ) (Unitriangular n ℝ))
      (GroupLieAlgebra 𝓘(ℝ, UnitriangularIndex n → ℝ) (Unitriangular n ℝ)) :=
  unitriangularNativeLie_isNilpotent

end Hindman168
