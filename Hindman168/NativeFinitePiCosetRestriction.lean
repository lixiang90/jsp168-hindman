import Hindman168.NativeFinitePiCubeProjection

/-! Actual restrictions (allowing repeated coordinates) of native product
quotients and cube vertices. No normality or chosen representative is assumed. -/
namespace Hindman168
universe u

noncomputable def nativeFinitePiCosetRestriction {ι κ : Type} [Fintype ι] [Fintype κ] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (select : κ → ι) :
    (nativeFinitePiData D).G ⧸ (nativeFinitePiData D).Γ →
      (nativeFinitePiData (D ∘ select)).G ⧸ (nativeFinitePiData (D ∘ select)).Γ :=
  fun x => (nativeFinitePiCosetHomeomorph (D ∘ select)).symm
    (fun k => nativeFinitePiCosetCoordinate D (select k) x)

theorem native_finite_pi_restriction_coordinate {ι κ : Type} [Fintype ι] [Fintype κ] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (select : κ → ι)
    (x : (nativeFinitePiData D).G ⧸ (nativeFinitePiData D).Γ) (k : κ) :
    nativeFinitePiCosetCoordinate (D ∘ select) k (nativeFinitePiCosetRestriction D select x) =
      nativeFinitePiCosetCoordinate D (select k) x := by
  rw [← native_finite_pi_coset_homeomorph_apply]
  exact congrFun ((nativeFinitePiCosetHomeomorph (D ∘ select)).apply_symm_apply _) k

theorem native_finite_pi_restriction_continuous {ι κ : Type} [Fintype ι] [Fintype κ] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (select : κ → ι) :
    Continuous (nativeFinitePiCosetRestriction D select) :=
  (nativeFinitePiCosetHomeomorph (D ∘ select)).symm.continuous.comp
    (continuous_pi (fun k => native_finite_pi_coset_coordinate_continuous D (select k)))

theorem native_finite_pi_metric_restriction_continuous {ι κ : Type} [Fintype ι] [Fintype κ] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (select : κ → ι) :
    let J := nativeFinitePiData D
    let K := nativeFinitePiData (D ∘ select)
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI := K.metric
    letI : TopologicalSpace (K.G ⧸ K.Γ) := K.metric.toUniformSpace.toTopologicalSpace
    Continuous (nativeFinitePiCosetRestriction D select) := by
  dsimp only
  rw [← nativeNilmanifold_metric_topology (nativeFinitePiData D),
    ← nativeNilmanifold_metric_topology (nativeFinitePiData (D ∘ select))]
  exact native_finite_pi_restriction_continuous D select

noncomputable def nativeFinitePiRestrictedCubeProjection {ι κ δ : Type} [Fintype ι] [Fintype κ] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (select : κ → ι) (vertex : κ → δ) :
    (δ → (nativeFinitePiData D).G ⧸ (nativeFinitePiData D).Γ) →
      (nativeFinitePiData (D ∘ select)).G ⧸ (nativeFinitePiData (D ∘ select)).Γ :=
  fun x => nativeFinitePiCubeProjection (D ∘ select) vertex
    (fun V => nativeFinitePiCosetRestriction D select (x V))

theorem native_finite_pi_restricted_cube_projection_continuous
    {ι κ δ : Type} [Fintype ι] [Fintype κ] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (select : κ → ι) (vertex : κ → δ) :
    Continuous (nativeFinitePiRestrictedCubeProjection D select vertex) :=
  (native_finite_pi_cube_projection_continuous (D ∘ select) vertex).comp
    (continuous_pi (fun V => (native_finite_pi_restriction_continuous D select).comp (continuous_apply V)))

theorem native_finite_pi_metric_restricted_cube_projection_continuous
    {ι κ δ : Type} [Fintype ι] [Fintype κ] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (select : κ → ι) (vertex : κ → δ) :
    let J := nativeFinitePiData D
    let K := nativeFinitePiData (D ∘ select)
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI := K.metric
    letI : TopologicalSpace (K.G ⧸ K.Γ) := K.metric.toUniformSpace.toTopologicalSpace
    Continuous (nativeFinitePiRestrictedCubeProjection D select vertex) := by
  dsimp only
  rw [← nativeNilmanifold_metric_topology (nativeFinitePiData D),
    ← nativeNilmanifold_metric_topology (nativeFinitePiData (D ∘ select))]
  exact native_finite_pi_restricted_cube_projection_continuous D select vertex

end Hindman168
