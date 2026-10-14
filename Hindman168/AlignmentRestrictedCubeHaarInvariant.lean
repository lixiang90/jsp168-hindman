import Hindman168.NativeFinitePiRestrictedCubeProjection
import Hindman168.AlignmentJointNativeSlotHomeomorph
import Hindman168.NativeResidueCubeHaarImage

/-! The literal same-source projected Haar measure equality, with all quotient
measurable structures and codomains specified explicitly. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff Classical
universe u

variable {ι κ : Type} [Fintype ι] [Fintype κ] {σ : ι → Type} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν + 1) → σ ν → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I)
      (G := (D ν).G) (n ν) (v ν))) (index : κ → ι)

def AlignmentRestrictedCubeHaarInvariant
    {ℓ : ℕ}
    (H : NativeRationalSubgroupFiltration
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) ℓ)
    (ρ : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
    (hρ : ρ ∈ nativeSubgroupRationalHull
      (E := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).E)
      (I := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).I)
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ)
    (d : ℕ)
    (h : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
    (vertex : κ → Finset (Fin d)) (slots : ∀ k, σ (index k) → ℤ) : Prop :=
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI : MeasurableSpace J.G := borel J.G
    let K := nativeFinitePiData (fun k => alignmentNativeArrayData
      (D (index k)) (n (index k)) (v (index k)) (hv (index k)))
    letI : MeasurableSpace K.G := borel K.G
    let π : (Finset (Fin d) → J.G ⧸ J.Γ) → K.G ⧸ K.Γ := nativeFinitePiRestrictedCubeProjection
      (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) index vertex
    let τ : (K.G ⧸ K.Γ) → K.G ⧸ K.Γ := alignmentJointNativeCosetSlotTranslation (D ∘ index) (n ∘ index)
      (fun k => v (index k)) (fun k => hv (index k)) slots
    Measure.map τ (Measure.map π
      (nativeResidueCubeHaarImage J H ρ hρ d (2^d-1) (nativeCubeVertexEnumeration d) h)) =
      Measure.map π (nativeResidueCubeHaarImage J H ρ hρ d (2^d-1) (nativeCubeVertexEnumeration d) h)

end Hindman168
