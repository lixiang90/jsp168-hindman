import Hindman168.NativeCenterTorusEquivalence
import Hindman168.CentralCosetAction
import Hindman168.NativeNilmanifoldProbabilityTesting

/-! Actual compact central torus action on the ORIGINAL cosets, preserving
the constructed ORIGINAL quotient probability in the specified metric. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

abbrev nativeNilmanifoldCenterIndex {s : ℕ} (D : NativeNilmanifoldData.{u} s) :=
  Fin (Module.finrank ℝ (nativeLieCenterModel (I := D.I) (G := D.G)))

noncomputable def nativeNilmanifoldCentralAction {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    UnitAddTorus (nativeNilmanifoldCenterIndex D) → (D.G ⧸ D.Γ) → (D.G ⧸ D.Γ) :=
  fun a q => centralCosetAction D.Γ ((nativeCenterTorusHomeomorph (I := D.I) D.Γ).symm a) q

theorem native_nilmanifold_central_action_mk {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (z : Subgroup.center D.G) (q : D.G ⧸ D.Γ) :
    nativeNilmanifoldCentralAction D (nativeCenterTorusProjection (I := D.I) D.Γ z) q =
      (z : D.G) • q := by
  rw [← native_center_torus_homeomorph_mk (I := D.I) D.Γ z]
  simp only [nativeNilmanifoldCentralAction, Homeomorph.symm_apply_apply, central_coset_action_mk]

theorem native_nilmanifold_central_action_zero {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (q : D.G ⧸ D.Γ) : nativeNilmanifoldCentralAction D 0 q = q := by
  rw [nativeNilmanifoldCentralAction, native_center_torus_homeomorph_symm_zero,
    central_coset_action_one]

theorem native_nilmanifold_central_action_add {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (a b : UnitAddTorus (nativeNilmanifoldCenterIndex D)) (q : D.G ⧸ D.Γ) :
    nativeNilmanifoldCentralAction D (a+b) q =
      nativeNilmanifoldCentralAction D a (nativeNilmanifoldCentralAction D b q) := by
  rw [nativeNilmanifoldCentralAction, native_center_torus_homeomorph_symm_add,
    central_coset_action_mul]
  rfl

theorem native_nilmanifold_central_action_commutes {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (a : UnitAddTorus (nativeNilmanifoldCenterIndex D)) (g : D.G) (q : D.G ⧸ D.Γ) :
    nativeNilmanifoldCentralAction D a (g • q) = g • nativeNilmanifoldCentralAction D a q :=
  central_coset_action_commutes D.Γ _ g q

theorem native_nilmanifold_central_action_continuous {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : UnitAddTorus (nativeNilmanifoldCenterIndex D) × (D.G ⧸ D.Γ) =>
      nativeNilmanifoldCentralAction D p.1 p.2) := by
  have h := (central_coset_action_continuous D.Γ).comp
    (((nativeCenterTorusHomeomorph (I := D.I) D.Γ).symm.continuous.comp continuous_fst).prodMk
      continuous_snd)
  exact Eq.mp (congrArg (fun t : TopologicalSpace (D.G ⧸ D.Γ) =>
    @Continuous (UnitAddTorus (nativeNilmanifoldCenterIndex D) × (D.G ⧸ D.Γ)) (D.G ⧸ D.Γ)
      (@instTopologicalSpaceProd _ _ inferInstance t) t
      (fun p => nativeNilmanifoldCentralAction D p.1 p.2))
        (nativeNilmanifold_metric_topology D)) h

theorem native_nilmanifold_central_action_probability {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (a : UnitAddTorus (nativeNilmanifoldCenterIndex D)) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    Measure.map (nativeNilmanifoldCentralAction D a) (nativeNilmanifoldQuotientProbability D) =
      nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  obtain ⟨z, hz⟩ := native_center_torus_projection_surjective (I := D.I) D.Γ a
  rw [← hz]
  have he : nativeNilmanifoldCentralAction D (nativeCenterTorusProjection (I := D.I) D.Γ z) =
      fun q => (z : D.G) • q := funext (native_nilmanifold_central_action_mk D z)
  rw [he]
  exact native_nilmanifold_quotient_probability_translate D z

theorem native_nilmanifold_central_action_integral {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (a : UnitAddTorus (nativeNilmanifoldCenterIndex D)) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    ∀ F : (D.G ⧸ D.Γ) → ℂ,
      (∫ q, F (nativeNilmanifoldCentralAction D a q) ∂nativeNilmanifoldQuotientProbability D) =
        ∫ q, F q ∂nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  intro F
  obtain ⟨z, hz⟩ := native_center_torus_projection_surjective (I := D.I) D.Γ a
  rw [← hz]
  simp only [native_nilmanifold_central_action_mk]
  exact native_nilmanifold_probability_integral_translation D z F

end Hindman168
