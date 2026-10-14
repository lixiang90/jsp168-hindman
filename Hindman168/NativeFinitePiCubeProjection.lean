import Hindman168.NativeFinitePiCosetCoordinates

/-! Actual coordinatewise vertex projection on a native product quotient.
Its construction uses the product-lattice quotient homeomorphism, not chosen
representatives or an assumed Lipschitz property. -/
namespace Hindman168
universe u

noncomputable def nativeFinitePiCosetHomeomorph {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) :
    (nativeFinitePiData D).G ⧸ (nativeFinitePiData D).Γ ≃ₜ (∀ i, (D i).G ⧸ (D i).Γ) :=
  piCosetHomeomorph (fun i => (D i).Γ)

theorem native_finite_pi_coset_homeomorph_apply {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s)
    (x : (nativeFinitePiData D).G ⧸ (nativeFinitePiData D).Γ) (i : ι) :
    nativeFinitePiCosetHomeomorph D x i = nativeFinitePiCosetCoordinate D i x := by
  induction x using Quotient.inductionOn with
  | _ g => rfl

noncomputable def nativeFinitePiCubeProjection {ι κ : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (vertex : ι → κ) :
    (κ → (nativeFinitePiData D).G ⧸ (nativeFinitePiData D).Γ) →
      (nativeFinitePiData D).G ⧸ (nativeFinitePiData D).Γ :=
  fun x => (nativeFinitePiCosetHomeomorph D).symm (fun i => nativeFinitePiCosetCoordinate D i (x (vertex i)))

theorem native_finite_pi_cube_projection_coordinate {ι κ : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (vertex : ι → κ)
    (x : κ → (nativeFinitePiData D).G ⧸ (nativeFinitePiData D).Γ) (i : ι) :
    nativeFinitePiCosetCoordinate D i (nativeFinitePiCubeProjection D vertex x) =
      nativeFinitePiCosetCoordinate D i (x (vertex i)) := by
  rw [← native_finite_pi_coset_homeomorph_apply]
  exact congrFun ((nativeFinitePiCosetHomeomorph D).apply_symm_apply _) i

theorem native_finite_pi_cube_projection_continuous {ι κ : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (vertex : ι → κ) :
    Continuous (nativeFinitePiCubeProjection D vertex) :=
  (nativeFinitePiCosetHomeomorph D).symm.continuous.comp
    (continuous_pi (fun i => (native_finite_pi_coset_coordinate_continuous D i).comp (continuous_apply (vertex i))))

theorem native_finite_pi_metric_cube_projection_continuous {ι κ : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (vertex : ι → κ) :
    let J := nativeFinitePiData D
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    Continuous (nativeFinitePiCubeProjection D vertex) := by
  dsimp only
  rw [← nativeNilmanifold_metric_topology (nativeFinitePiData D)]
  exact native_finite_pi_cube_projection_continuous D vertex

end Hindman168
