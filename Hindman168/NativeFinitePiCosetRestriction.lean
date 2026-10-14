import Hindman168.NativeFinitePiCubeProjection
import Hindman168.PiCosetRestriction

/-! Restriction of a genuine heterogeneous finite product quotient to a
subfamily. This uses the proved product quotient homeomorphisms and requires
no choices of coset representatives, Haar law, or Lipschitz hypothesis. -/
namespace Hindman168
universe u

variable {ι κ : Type} [Fintype ι] [Fintype κ] {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (index : κ → ι)

noncomputable def nativeFinitePiCosetRestriction :
    (nativeFinitePiData D).G ⧸ (nativeFinitePiData D).Γ →
      (nativeFinitePiData (D ∘ index)).G ⧸ (nativeFinitePiData (D ∘ index)).Γ :=
  piCosetRestriction (fun i => (D i).Γ) index

theorem native_finite_pi_coset_restriction_coordinate
    (x : (nativeFinitePiData D).G ⧸ (nativeFinitePiData D).Γ) (k : κ) :
    nativeFinitePiCosetCoordinate (D ∘ index) k
      (nativeFinitePiCosetRestriction D index x) =
      nativeFinitePiCosetCoordinate D (index k) x := by
  induction x using Quotient.inductionOn with
  | _ g =>
    change nativeFinitePiCosetCoordinate (D ∘ index) k
      (piCosetRestriction (fun i => (D i).Γ) index (QuotientGroup.mk g)) = _
    rw [piCosetRestriction_mk]
    rfl

theorem native_finite_pi_coset_restriction_continuous :
    Continuous (nativeFinitePiCosetRestriction D index) :=
  piCosetRestriction_continuous (fun i => (D i).Γ) index

theorem native_finite_pi_coset_restriction_mk
    (g : (nativeFinitePiData D).G) :
    nativeFinitePiCosetRestriction D index
      (g : (nativeFinitePiData D).G ⧸ (nativeFinitePiData D).Γ) =
      (nativeFinitePiGroupValue (D ∘ index)
        (fun k => nativeFinitePiGroupEquiv D g (index k)) :
          (nativeFinitePiData (D ∘ index)).G ⧸ (nativeFinitePiData (D ∘ index)).Γ) :=
  piCosetRestriction_mk (fun i => (D i).Γ) index g

theorem native_finite_pi_coset_restriction_cube_projection
    {V : Type} (vertex : ι → V)
    (x : V → (nativeFinitePiData D).G ⧸ (nativeFinitePiData D).Γ) :
    nativeFinitePiCosetRestriction D index (nativeFinitePiCubeProjection D vertex x) =
      nativeFinitePiCubeProjection (D ∘ index) (vertex ∘ index)
        (fun z => nativeFinitePiCosetRestriction D index (x z)) := by
  apply (nativeFinitePiCosetHomeomorph (D ∘ index)).injective
  funext k
  rw [native_finite_pi_coset_homeomorph_apply (D ∘ index),
    native_finite_pi_coset_homeomorph_apply (D ∘ index)]
  rw [native_finite_pi_coset_restriction_coordinate,
    native_finite_pi_cube_projection_coordinate,
    native_finite_pi_cube_projection_coordinate,
    native_finite_pi_coset_restriction_coordinate]
  rfl

theorem native_finite_pi_metric_coset_restriction_continuous :
    let J := nativeFinitePiData D
    let K := nativeFinitePiData (D ∘ index)
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI := K.metric
    letI : TopologicalSpace (K.G ⧸ K.Γ) := K.metric.toUniformSpace.toTopologicalSpace
    Continuous (nativeFinitePiCosetRestriction D index) := by
  dsimp only
  rw [← nativeNilmanifold_metric_topology (nativeFinitePiData D),
    ← nativeNilmanifold_metric_topology (nativeFinitePiData (D ∘ index))]
  exact native_finite_pi_coset_restriction_continuous D index

end Hindman168
