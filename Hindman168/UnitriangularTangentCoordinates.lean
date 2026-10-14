import Hindman168.UnitriangularLieGroup
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-! Actual native tangent coordinates for the global unitriangular chart.
The chart derivative is computed from the native manifold derivative,
and the vector-field bracket is reduced to ordinary coordinate calculus. -/

namespace Hindman168
open Matrix Set Topology
open scoped Manifold ContDiff

variable {n : ℕ}

 theorem unitriangular_chart_source (g : Unitriangular n ℝ) :
    (chartAt (UnitriangularIndex n → ℝ) g).source = univ := rfl

 theorem unitriangular_extChartAt_coe (g : Unitriangular n ℝ) :
    ⇑(extChartAt 𝓘(ℝ, UnitriangularIndex n → ℝ) g) =
      (unitriangularCoordinates : Unitriangular n ℝ → (UnitriangularIndex n → ℝ)) := rfl

 theorem unitriangular_extChartAt_inverse_coe (g : Unitriangular n ℝ) :
    ⇑(extChartAt 𝓘(ℝ, UnitriangularIndex n → ℝ) g).symm =
      (unitriangularCoordinatesEquiv.symm : (UnitriangularIndex n → ℝ) → Unitriangular n ℝ) := by
  funext t
  have ht : unitriangularCoordinates (unitriangularCoordinatesEquiv.symm t) = t :=
    unitriangularCoordinatesEquiv.apply_symm_apply t
  calc
    (extChartAt 𝓘(ℝ, UnitriangularIndex n → ℝ) g).symm t =
        (extChartAt 𝓘(ℝ, UnitriangularIndex n → ℝ) g).symm
          (unitriangularCoordinates (unitriangularCoordinatesEquiv.symm t)) := by rw [ht]
    _ = unitriangularCoordinatesEquiv.symm t := by
      change (extChartAt 𝓘(ℝ, UnitriangularIndex n → ℝ) g).symm
        (extChartAt 𝓘(ℝ, UnitriangularIndex n → ℝ) g (unitriangularCoordinatesEquiv.symm t)) =
        unitriangularCoordinatesEquiv.symm t
      exact (extChartAt 𝓘(ℝ, UnitriangularIndex n → ℝ) g).left_inv (by
        rw [extChartAt_source, unitriangular_chart_source]
        exact mem_univ _)

 theorem unitriangularCoordinates_mfderiv (g : Unitriangular n ℝ) :
    mfderiv 𝓘(ℝ, UnitriangularIndex n → ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ)
      unitriangularCoordinates g = ContinuousLinearMap.id ℝ (UnitriangularIndex n → ℝ) := by
  have h := mfderiv_extChartAt_self (I := 𝓘(ℝ, UnitriangularIndex n → ℝ)) (x := g)
  rw [unitriangular_extChartAt_coe] at h
  exact h

 theorem unitriangularCoordinates_inverse_mfderiv (t : UnitriangularIndex n → ℝ) :
    mfderiv 𝓘(ℝ, UnitriangularIndex n → ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ)
      (unitriangularCoordinatesEquiv.symm : (UnitriangularIndex n → ℝ) → Unitriangular n ℝ) t =
      ContinuousLinearMap.id ℝ (UnitriangularIndex n → ℝ) := by
  have h := mfderivWithin_range_extChartAt_symm
    (I := 𝓘(ℝ, UnitriangularIndex n → ℝ)) (x := unitriangularCoordinatesEquiv.symm t)
  rw [unitriangular_extChartAt_inverse_coe, unitriangular_extChartAt_coe,
    ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
  have ht : unitriangularCoordinates (unitriangularCoordinatesEquiv.symm t) = t :=
    unitriangularCoordinatesEquiv.apply_symm_apply t
  change mfderiv 𝓘(ℝ, UnitriangularIndex n → ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ)
    (unitriangularCoordinatesEquiv.symm : (UnitriangularIndex n → ℝ) → Unitriangular n ℝ)
    (unitriangularCoordinates (unitriangularCoordinatesEquiv.symm t)) =
    ContinuousLinearMap.id ℝ (UnitriangularIndex n → ℝ) at h
  rw [ht] at h
  exact h

 theorem unitriangular_mfderiv_eq_chart_fderiv (f : Unitriangular n ℝ → Unitriangular n ℝ)
    (g : Unitriangular n ℝ)
    (hf : MDifferentiableAt 𝓘(ℝ, UnitriangularIndex n → ℝ)
      𝓘(ℝ, UnitriangularIndex n → ℝ) f g) :
    mfderiv 𝓘(ℝ, UnitriangularIndex n → ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ) f g =
      fderiv ℝ (unitriangularCoordinates ∘ f ∘ unitriangularCoordinatesEquiv.symm)
        (unitriangularCoordinates g) := by
  rw [mfderiv, if_pos hf]
  simp only [writtenInExtChartAt, unitriangular_extChartAt_coe,
    unitriangular_extChartAt_inverse_coe, ModelWithCorners.range_eq_univ,
    fderivWithin_univ]

 theorem unitriangular_mlieBracket_coordinates
    (V W : Π g : Unitriangular n ℝ, TangentSpace 𝓘(ℝ, UnitriangularIndex n → ℝ) g)
    (g : Unitriangular n ℝ) :
    VectorField.mlieBracket 𝓘(ℝ, UnitriangularIndex n → ℝ) V W g =
      VectorField.lieBracket ℝ
        (fun t : UnitriangularIndex n → ℝ => V (unitriangularCoordinatesEquiv.symm t))
        (fun t : UnitriangularIndex n → ℝ => W (unitriangularCoordinatesEquiv.symm t))
        (unitriangularCoordinates g) := by
  rw [VectorField.mlieBracket, VectorField.mlieBracketWithin_apply]
  change (mfderiv 𝓘(ℝ, UnitriangularIndex n → ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ)
    unitriangularCoordinates g : (UnitriangularIndex n → ℝ) →L[ℝ] (UnitriangularIndex n → ℝ)).inverse
    (VectorField.lieBracketWithin (E := UnitriangularIndex n → ℝ) ℝ
      (VectorField.mpullbackWithin 𝓘(ℝ, UnitriangularIndex n → ℝ)
        𝓘(ℝ, UnitriangularIndex n → ℝ)
        (extChartAt 𝓘(ℝ, UnitriangularIndex n → ℝ) g).symm V
        (range 𝓘(ℝ, UnitriangularIndex n → ℝ)))
      (VectorField.mpullbackWithin 𝓘(ℝ, UnitriangularIndex n → ℝ)
        𝓘(ℝ, UnitriangularIndex n → ℝ)
        (extChartAt 𝓘(ℝ, UnitriangularIndex n → ℝ) g).symm W
        (range 𝓘(ℝ, UnitriangularIndex n → ℝ)))
      ((extChartAt 𝓘(ℝ, UnitriangularIndex n → ℝ) g).symm ⁻¹' univ ∩
        range 𝓘(ℝ, UnitriangularIndex n → ℝ)) (unitriangularCoordinates g)) = _
  erw [unitriangularCoordinates_mfderiv, ContinuousLinearMap.inverse_id]
  simp only [unitriangular_extChartAt_inverse_coe,
    ModelWithCorners.range_eq_univ, preimage_univ, inter_univ]
  have hpb (U : Π g : Unitriangular n ℝ, TangentSpace 𝓘(ℝ, UnitriangularIndex n → ℝ) g) :
      VectorField.mpullbackWithin 𝓘(ℝ, UnitriangularIndex n → ℝ)
        𝓘(ℝ, UnitriangularIndex n → ℝ) unitriangularCoordinatesEquiv.symm U univ =
      fun t : UnitriangularIndex n → ℝ => U (unitriangularCoordinatesEquiv.symm t) := by
    funext t
    rw [VectorField.mpullbackWithin_apply, mfderivWithin_univ]
    erw [unitriangularCoordinates_inverse_mfderiv, ContinuousLinearMap.inverse_id]
    rfl
  rw [hpb V, hpb W, VectorField.lieBracketWithin_univ]
  rfl

end Hindman168
