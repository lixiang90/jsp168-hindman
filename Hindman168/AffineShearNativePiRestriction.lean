import Hindman168.NativeFinitePiData
import Hindman168.AffineShearCosetImage

/-! The original heterogeneous-product restriction is a genuine smooth
lattice-compatible group homomorphism, so its image filtration can be
constructed by the generic native homomorphism results. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def affineShearNativePiRestriction {ι κ : Type} [Fintype ι] [Fintype κ]
    {s : ℕ} (D : ι → NativeNilmanifoldData.{u} s) (index : κ → ι) :
    (nativeFinitePiData D).G →* (nativeFinitePiData (D ∘ index)).G where
  toFun g k := g (index k)
  map_one' := rfl
  map_mul' _ _ := rfl

 theorem affineShear_native_pi_restriction_lattice {ι κ : Type} [Fintype ι] [Fintype κ]
    {s : ℕ} (D : ι → NativeNilmanifoldData.{u} s) (index : κ → ι)
    (g : (nativeFinitePiData D).G) (hg : g ∈ (nativeFinitePiData D).Γ) :
    affineShearNativePiRestriction D index g ∈ (nativeFinitePiData (D ∘ index)).Γ := by
  rw [native_finite_pi_lattice_mem] at hg ⊢
  exact fun k => hg (index k)

 theorem affineShear_native_pi_restriction_smooth {ι κ : Type} [Fintype ι] [Fintype κ]
    {s : ℕ} (D : ι → NativeNilmanifoldData.{u} s) (index : κ → ι) :
    ContMDiff (nativeFinitePiData D).I (nativeFinitePiData (D ∘ index)).I ∞
      (affineShearNativePiRestriction D index : (nativeFinitePiData D).G →
        (nativeFinitePiData (D ∘ index)).G) := by
  let e := fun i => nativeLieExponentialDiffeomorph (E := (D i).E) (I := (D i).I) (G := (D i).G)
  letI := finitePiGroupChartedSpace e
  letI := finitePiGroupChartedSpace (fun k => e (index k))
  let d := finitePiGroupDiffeomorph e
  have h : ContMDiff 𝓘(ℝ, ∀ i, (D i).E) 𝓘(ℝ, ∀ k, (D (index k)).E) ∞
      (fun x k => d x (index k)) := by
    apply finitePiGroup_contMDiff_from_normed (fun k => e (index k))
    intro k
    have hp : ContDiff ℝ ∞ (fun x : ∀ i, (D i).E => x (index k)) :=
      contDiff_pi.mp contDiff_id (index k)
    exact (e (index k)).contMDiff_toFun.comp hp.contMDiff
  exact (h.comp d.contMDiff_invFun).congr (fun g => by
    change (fun k => g (index k)) = (fun k => d (d.symm g) (index k))
    rw [d.apply_symm_apply])

end Hindman168
