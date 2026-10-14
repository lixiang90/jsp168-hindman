import Hindman168.CentralFactorCosetFibers
import Hindman168.NativeCenterQuotientLattice
import Hindman168.NativeCentralFourierProjection

/-! The genuine original central factor with actual compact/Hausdorff topology. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

abbrev nativeCentralFactorSpace {s : ℕ} (D : NativeNilmanifoldData.{u} s) :=
  (D.G ⧸ Subgroup.center D.G) ⧸ D.Γ.map (QuotientGroup.mk' (Subgroup.center D.G))

theorem native_central_factor_compact {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    CompactSpace (nativeCentralFactorSpace D) :=
  nativeLattice_center_quotient_image_cocompact D.Γ

theorem native_central_factor_hausdorff {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    T2Space (nativeCentralFactorSpace D) := by
  letI : IsClosed (Subgroup.center D.G : Set D.G) := center_isClosed
  letI := nativeLattice_center_quotient_image_discrete (I := D.I) D.Γ
  letI : IsClosed (D.Γ.map (QuotientGroup.mk' (Subgroup.center D.G)) : Set (D.G ⧸ Subgroup.center D.G)) :=
    Subgroup.isClosed_of_discrete
  infer_instance

theorem native_central_factor_metric_openQuotient {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsOpenQuotientMap (centralFactorCosetMap D.Γ) := by
  exact Eq.mp (congrArg (fun t : TopologicalSpace (D.G ⧸ D.Γ) =>
    @IsOpenQuotientMap (D.G ⧸ D.Γ) (nativeCentralFactorSpace D) t inferInstance
      (centralFactorCosetMap D.Γ)) (nativeNilmanifold_metric_topology D))
        (central_factor_coset_map_openQuotient D.Γ)

theorem native_central_factor_torus_fiber_iff {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (q r : D.G ⧸ D.Γ) : centralFactorCosetMap D.Γ q = centralFactorCosetMap D.Γ r ↔
      ∃ a : UnitAddTorus (nativeNilmanifoldCenterIndex D), r = nativeNilmanifoldCentralAction D a q := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (central_factor_coset_map_fiber_iff D.Γ q r).mp h
    refine ⟨nativeCenterTorusProjection (I := D.I) D.Γ z, ?_⟩
    rw [native_nilmanifold_central_action_mk]
    exact hz
  · rintro ⟨a, rfl⟩
    obtain ⟨z, rfl⟩ := native_center_torus_projection_surjective (I := D.I) D.Γ a
    rw [native_nilmanifold_central_action_mk]
    exact (central_factor_coset_map_central D.Γ z q).symm

end Hindman168
