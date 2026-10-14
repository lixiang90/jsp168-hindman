import Hindman168.NativeCentralSubspaceTorusEquivalence
import Hindman168.NativeNilmanifoldProbabilityTesting

/-! ACTUAL rational central-subspace torus action on SAME original
specified-metric cosets, preserving ACTUAL original canonical Haar. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

variable {s : ℕ} (D : NativeNilmanifoldData.{u} s) (V : Submodule ℝ D.E)
  (hV : V ≤ nativeLieCenterModel (I := D.I) (G := D.G))
  (hrat : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ V)
local notation "N" => nativeCentralSubspaceSubgroup (I := D.I) V hV

noncomputable def nativeNilmanifoldSubspaceAction :
    UnitAddTorus (Fin (Module.finrank ℝ V)) → (D.G ⧸ D.Γ) → (D.G ⧸ D.Γ) :=
  fun a q => centralSubgroupCosetAction N D.Γ (nativeCentralSubspaceSubgroup_le_center V hV)
    ((nativeCentralSubspaceTorusHomeomorph (I := D.I) D.Γ V hV hrat).symm a) q

theorem native_nilmanifold_subspace_action_mk (z : N) (q : D.G ⧸ D.Γ) :
    nativeNilmanifoldSubspaceAction D V hV hrat
      (nativeCentralSubspaceTorusProjection (I := D.I) D.Γ V hV hrat z) q = (z : D.G) • q := by
  rw [← native_central_subspace_torus_homeomorph_mk (I := D.I) D.Γ V hV hrat z]
  simp only [nativeNilmanifoldSubspaceAction,Homeomorph.symm_apply_apply,central_subgroup_coset_action_mk]

theorem native_nilmanifold_subspace_action_zero (q : D.G ⧸ D.Γ) :
    nativeNilmanifoldSubspaceAction D V hV hrat 0 q = q := by
  letI := central_subgroup_lattice_normal N D.Γ (nativeCentralSubspaceSubgroup_le_center V hV)
  rw [nativeNilmanifoldSubspaceAction,native_central_subspace_torus_homeomorph_symm_zero,
    central_subgroup_coset_action_one]

theorem native_nilmanifold_subspace_action_add
    (a b : UnitAddTorus (Fin (Module.finrank ℝ V))) (q : D.G ⧸ D.Γ) :
    nativeNilmanifoldSubspaceAction D V hV hrat (a+b) q =
      nativeNilmanifoldSubspaceAction D V hV hrat a (nativeNilmanifoldSubspaceAction D V hV hrat b q) := by
  letI := central_subgroup_lattice_normal N D.Γ (nativeCentralSubspaceSubgroup_le_center V hV)
  rw [nativeNilmanifoldSubspaceAction,native_central_subspace_torus_homeomorph_symm_add,
    central_subgroup_coset_action_mul]
  rfl

theorem native_nilmanifold_subspace_action_commutes
    (a : UnitAddTorus (Fin (Module.finrank ℝ V))) (g : D.G) (q : D.G ⧸ D.Γ) :
    nativeNilmanifoldSubspaceAction D V hV hrat a (g • q) =
      g • nativeNilmanifoldSubspaceAction D V hV hrat a q :=
  central_subgroup_coset_action_commutes N D.Γ (nativeCentralSubspaceSubgroup_le_center V hV) _ g q

theorem native_nilmanifold_subspace_action_continuous :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : UnitAddTorus (Fin (Module.finrank ℝ V)) × (D.G ⧸ D.Γ) =>
      nativeNilmanifoldSubspaceAction D V hV hrat p.1 p.2) := by
  have h := (central_subgroup_coset_action_continuous N D.Γ
    (nativeCentralSubspaceSubgroup_le_center V hV)).comp
    (((nativeCentralSubspaceTorusHomeomorph (I := D.I) D.Γ V hV hrat).symm.continuous.comp continuous_fst).prodMk
      continuous_snd)
  exact Eq.mp (congrArg (fun t : TopologicalSpace (D.G ⧸ D.Γ) =>
    @Continuous (UnitAddTorus (Fin (Module.finrank ℝ V)) × (D.G ⧸ D.Γ)) (D.G ⧸ D.Γ)
      (@instTopologicalSpaceProd _ _ inferInstance t) t
      (fun p => nativeNilmanifoldSubspaceAction D V hV hrat p.1 p.2))
        (nativeNilmanifold_metric_topology D)) h

theorem native_nilmanifold_subspace_action_probability
    (a : UnitAddTorus (Fin (Module.finrank ℝ V))) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    Measure.map (nativeNilmanifoldSubspaceAction D V hV hrat a) (nativeNilmanifoldQuotientProbability D) =
      nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  obtain ⟨z,hz⟩ := native_central_subspace_torus_projection_surjective (I := D.I) D.Γ V hV hrat a
  rw [← hz]
  have he : nativeNilmanifoldSubspaceAction D V hV hrat
      (nativeCentralSubspaceTorusProjection (I := D.I) D.Γ V hV hrat z) =
      fun q => (z : D.G) • q := funext (native_nilmanifold_subspace_action_mk D V hV hrat z)
  rw [he]
  exact native_nilmanifold_quotient_probability_translate D z

theorem native_nilmanifold_subspace_action_integral
    (a : UnitAddTorus (Fin (Module.finrank ℝ V))) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    ∀ F : (D.G ⧸ D.Γ) → ℂ,
      (∫ q, F (nativeNilmanifoldSubspaceAction D V hV hrat a q) ∂nativeNilmanifoldQuotientProbability D) =
        ∫ q, F q ∂nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  intro F
  obtain ⟨z,hz⟩ := native_central_subspace_torus_projection_surjective (I := D.I) D.Γ V hV hrat a
  rw [← hz]
  simp only [native_nilmanifold_subspace_action_mk]
  exact native_nilmanifold_probability_integral_translation D z F

end Hindman168
