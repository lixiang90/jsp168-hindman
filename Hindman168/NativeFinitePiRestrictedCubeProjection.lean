import Hindman168.NativeFinitePiCosetRestriction

/-! The cube projection of an arbitrary subfamily of one genuine finite
native product quotient. Different subfamilies need not choose the same
vertex at a common coordinate. Every projection is built from the actual
quotient homeomorphisms, with no representative or Lipschitz oracle. -/
namespace Hindman168
universe u

variable {ι κ V : Type} [Fintype ι] [Fintype κ] {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (index : κ → ι) (vertex : κ → V)

noncomputable def nativeFinitePiRestrictedCubeProjection :
    (V → (nativeFinitePiData D).G ⧸ (nativeFinitePiData D).Γ) →
      (nativeFinitePiData (D ∘ index)).G ⧸ (nativeFinitePiData (D ∘ index)).Γ :=
  fun x => nativeFinitePiCubeProjection (D ∘ index) vertex
    (fun z => nativeFinitePiCosetRestriction D index (x z))

theorem native_finite_pi_restricted_cube_projection_coordinate
    (x : V → (nativeFinitePiData D).G ⧸ (nativeFinitePiData D).Γ) (k : κ) :
    nativeFinitePiCosetCoordinate (D ∘ index) k
      (nativeFinitePiRestrictedCubeProjection D index vertex x) =
      nativeFinitePiCosetCoordinate D (index k) (x (vertex k)) := by
  rw [nativeFinitePiRestrictedCubeProjection,
    native_finite_pi_cube_projection_coordinate,
    native_finite_pi_coset_restriction_coordinate]

theorem native_finite_pi_restricted_cube_projection_continuous :
    Continuous (nativeFinitePiRestrictedCubeProjection D index vertex) :=
  (native_finite_pi_cube_projection_continuous (D ∘ index) vertex).comp
    (continuous_pi (fun z =>
      (native_finite_pi_coset_restriction_continuous D index).comp (continuous_apply z)))

theorem native_finite_pi_metric_restricted_cube_projection_continuous :
    let J := nativeFinitePiData D
    let K := nativeFinitePiData (D ∘ index)
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI := K.metric
    letI : TopologicalSpace (K.G ⧸ K.Γ) := K.metric.toUniformSpace.toTopologicalSpace
    Continuous (nativeFinitePiRestrictedCubeProjection D index vertex) := by
  dsimp only
  rw [← nativeNilmanifold_metric_topology (nativeFinitePiData D),
    ← nativeNilmanifold_metric_topology (nativeFinitePiData (D ∘ index))]
  exact native_finite_pi_restricted_cube_projection_continuous D index vertex

end Hindman168
