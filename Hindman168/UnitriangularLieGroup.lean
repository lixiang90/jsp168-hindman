import Hindman168.UnitriangularCoordinates
import Hindman168.MatrixSmoothOperations
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Diffeomorph

/-! The native smooth Lie-group structure of the actual real unitriangular
matrix group. The original group operations and topology are unchanged.
A global coordinate chart and the actual finite matrix formulas prove all
smoothness assertions; no smooth group operation is supplied as a premise. -/

namespace Hindman168
open Matrix Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

variable {n : ℕ} {r : ℕ∞ω}

 theorem unitriangularCoordinateMatrix_contDiff :
    ContDiff ℝ r (unitriangularCoordinateMatrix : (UnitriangularIndex n → ℝ) →
      Matrix (Fin n) (Fin n) ℝ) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  by_cases hij : i < j
  · simpa only [unitriangularCoordinateMatrix, dif_pos hij] using
      (contDiff_apply ℝ ℝ (⟨toLex (OrderDual.toDual i, j), hij⟩ : UnitriangularIndex n))
  · simp only [unitriangularCoordinateMatrix, dif_neg hij]
    exact contDiff_const

 theorem unitriangularCoordinateMul_contDiff :
    ContDiff ℝ r (fun t : (UnitriangularIndex n → ℝ) × (UnitriangularIndex n → ℝ) =>
      unitriangularCoordinates (unitriangularCoordinatesEquiv.symm t.1 *
        unitriangularCoordinatesEquiv.symm t.2)) := by
  apply contDiff_pi.mpr
  intro p
  change ContDiff ℝ r (fun t : (UnitriangularIndex n → ℝ) × (UnitriangularIndex n → ℝ) =>
    (unitriangularCoordinateMatrix t.1 * unitriangularCoordinateMatrix t.2)
      (unitriangularRow p) (unitriangularColumn p))
  exact (contDiff_apply_apply ℝ ℝ (unitriangularRow p) (unitriangularColumn p)).comp
    (contDiff_matrix_mul (unitriangularCoordinateMatrix_contDiff.comp contDiff_fst)
      (unitriangularCoordinateMatrix_contDiff.comp contDiff_snd))

 theorem unitriangularCoordinateInv_contDiff :
    ContDiff ℝ r (fun t : UnitriangularIndex n → ℝ =>
      unitriangularCoordinates (unitriangularCoordinatesEquiv.symm t)⁻¹) := by
  apply contDiff_pi.mpr
  intro p
  have heq : (fun t : UnitriangularIndex n → ℝ =>
      unitriangularCoordinates (unitriangularCoordinatesEquiv.symm t)⁻¹ p) =
      fun t => (unitriangularCoordinateMatrix t).adjugate
        (unitriangularRow p) (unitriangularColumn p) := by
    funext t
    exact congrArg (fun A : Matrix (Fin n) (Fin n) ℝ =>
      A (unitriangularRow p) (unitriangularColumn p)) (unitriangular_inverse_adjugate _)
  rw [heq]
  exact (contDiff_apply_apply ℝ ℝ (unitriangularRow p) (unitriangularColumn p)).comp
    (contDiff_matrix_adjugate unitriangularCoordinateMatrix_contDiff)

 noncomputable instance unitriangularChartedSpace (n : ℕ) :
    ChartedSpace (UnitriangularIndex n → ℝ) (Unitriangular n ℝ) :=
  (unitriangularCoordinatesHomeomorph : Unitriangular n ℝ ≃ₜ
    (UnitriangularIndex n → ℝ)).isOpenEmbedding.singletonChartedSpace

 instance unitriangularIsManifold (n : ℕ) (r : ℕ∞ω) :
    IsManifold 𝓘(ℝ, UnitriangularIndex n → ℝ) r (Unitriangular n ℝ) :=
  (unitriangularCoordinatesHomeomorph : Unitriangular n ℝ ≃ₜ
    (UnitriangularIndex n → ℝ)).isOpenEmbedding.isManifold_singleton

 theorem unitriangularCoordinates_contMDiff :
    ContMDiff 𝓘(ℝ, UnitriangularIndex n → ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ) r
      (unitriangularCoordinates : Unitriangular n ℝ → (UnitriangularIndex n → ℝ)) :=
  contMDiff_isOpenEmbedding (unitriangularCoordinatesHomeomorph : Unitriangular n ℝ ≃ₜ
    (UnitriangularIndex n → ℝ)).isOpenEmbedding

 theorem unitriangularCoordinates_inverse_contMDiff :
    ContMDiff 𝓘(ℝ, UnitriangularIndex n → ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ) r
      (unitriangularCoordinatesEquiv.symm : (UnitriangularIndex n → ℝ) → Unitriangular n ℝ) := by
  apply ContMDiff.of_comp_isOpenEmbedding (unitriangularCoordinatesHomeomorph :
    Unitriangular n ℝ ≃ₜ (UnitriangularIndex n → ℝ)).isOpenEmbedding
  have heq : unitriangularCoordinates ∘ (unitriangularCoordinatesEquiv.symm :
      (UnitriangularIndex n → ℝ) → Unitriangular n ℝ) = id :=
    funext unitriangularCoordinatesEquiv.apply_symm_apply
  change ContMDiff 𝓘(ℝ, UnitriangularIndex n → ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ) r
    (unitriangularCoordinates ∘ (unitriangularCoordinatesEquiv.symm :
      (UnitriangularIndex n → ℝ) → Unitriangular n ℝ))
  rw [heq]
  exact contMDiff_id

 noncomputable def unitriangularCoordinatesDiffeomorph :
    Diffeomorph 𝓘(ℝ, UnitriangularIndex n → ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ)
      (Unitriangular n ℝ) (UnitriangularIndex n → ℝ) r where
  toEquiv := unitriangularCoordinatesEquiv
  contMDiff_toFun := unitriangularCoordinates_contMDiff
  contMDiff_invFun := unitriangularCoordinates_inverse_contMDiff

 theorem unitriangular_mul_contMDiff :
    ContMDiff (𝓘(ℝ, UnitriangularIndex n → ℝ).prod 𝓘(ℝ, UnitriangularIndex n → ℝ))
      𝓘(ℝ, UnitriangularIndex n → ℝ) r
      (fun t : Unitriangular n ℝ × Unitriangular n ℝ => t.1 * t.2) := by
  apply ContMDiff.of_comp_isOpenEmbedding (unitriangularCoordinatesHomeomorph :
    Unitriangular n ℝ ≃ₜ (UnitriangularIndex n → ℝ)).isOpenEmbedding
  have hc : ContMDiff
      (𝓘(ℝ, UnitriangularIndex n → ℝ).prod 𝓘(ℝ, UnitriangularIndex n → ℝ))
      𝓘(ℝ, (UnitriangularIndex n → ℝ) × (UnitriangularIndex n → ℝ)) r
      (fun t : Unitriangular n ℝ × Unitriangular n ℝ =>
        (unitriangularCoordinates t.1, unitriangularCoordinates t.2)) :=
    (unitriangularCoordinates_contMDiff.comp contMDiff_fst).prodMk_space
      (unitriangularCoordinates_contMDiff.comp contMDiff_snd)
  have hm := unitriangularCoordinateMul_contDiff.contMDiff.comp hc
  change ContMDiff
    (𝓘(ℝ, UnitriangularIndex n → ℝ).prod 𝓘(ℝ, UnitriangularIndex n → ℝ))
    𝓘(ℝ, UnitriangularIndex n → ℝ) r
    (fun t : Unitriangular n ℝ × Unitriangular n ℝ => unitriangularCoordinates (t.1 * t.2))
  have hleft (g : Unitriangular n ℝ) :
      unitriangularCoordinatesEquiv.symm (unitriangularCoordinates g) = g :=
    unitriangularCoordinatesEquiv.symm_apply_apply g
  simpa only [Function.comp_def, hleft] using hm

 theorem unitriangular_inv_contMDiff :
    ContMDiff 𝓘(ℝ, UnitriangularIndex n → ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ) r
      (fun g : Unitriangular n ℝ => g⁻¹) := by
  apply ContMDiff.of_comp_isOpenEmbedding (unitriangularCoordinatesHomeomorph :
    Unitriangular n ℝ ≃ₜ (UnitriangularIndex n → ℝ)).isOpenEmbedding
  have hi := unitriangularCoordinateInv_contDiff.contMDiff.comp
    (unitriangularCoordinates_contMDiff (n := n) (r := r))
  change ContMDiff 𝓘(ℝ, UnitriangularIndex n → ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ) r
    (fun g : Unitriangular n ℝ => unitriangularCoordinates g⁻¹)
  have hleft (g : Unitriangular n ℝ) :
      unitriangularCoordinatesEquiv.symm (unitriangularCoordinates g) = g :=
    unitriangularCoordinatesEquiv.symm_apply_apply g
  simpa only [Function.comp_def, hleft] using hi

 instance unitriangularLieGroup (n : ℕ) (r : ℕ∞ω) :
    LieGroup 𝓘(ℝ, UnitriangularIndex n → ℝ) r (Unitriangular n ℝ) where
  contMDiff_mul := unitriangular_mul_contMDiff
  contMDiff_inv := unitriangular_inv_contMDiff

end Hindman168
