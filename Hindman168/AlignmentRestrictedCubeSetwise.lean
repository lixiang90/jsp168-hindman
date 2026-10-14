import Hindman168.NativeFinitePiRestrictedCubeProjection
import Hindman168.AlignmentJointNativeSlotHomeomorph
import Hindman168.NativeProjectedCubeSupport

/-! A face symmetry of a target's marginal of the full joint Haar measure
preserves its actual projected cube orbit setwise. The projection is the
real subfamily restriction and the slot map is its proved homeomorphism.
No separately extracted target filtration or support hypothesis is used. -/
namespace Hindman168
open Set MeasureTheory
open scoped Manifold ContDiff Classical
universe u

variable {ι κ : Type} [Fintype ι] [Fintype κ] {σ : ι → Type} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν + 1) → σ ν → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I)
      (G := (D ν).G) (n ν) (v ν))) (index : κ → ι)

theorem alignment_restricted_cube_measure_symmetry_preserves_coset
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
    (vertex : κ → Finset (Fin d)) (slots : ∀ k, σ (index k) → ℤ) :
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
      Measure.map π (nativeResidueCubeHaarImage J H ρ hρ d (2^d-1) (nativeCubeVertexEnumeration d) h) →
    τ '' range (π ∘ nativeResidueCubeOrbitMap J H ρ hρ d (2^d-1) (nativeCubeVertexEnumeration d) h) =
      range (π ∘ nativeResidueCubeOrbitMap J H ρ hρ d (2^d-1) (nativeCubeVertexEnumeration d) h) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  let K := nativeFinitePiData (fun k => alignmentNativeArrayData
    (D (index k)) (n (index k)) (v (index k)) (hv (index k)))
  letI : MeasurableSpace J.G := borel J.G
  letI : MeasurableSpace K.G := borel K.G
  letI : T2Space (K.G ⧸ K.Γ) := by
    have hmetric : @T2Space (K.G ⧸ K.Γ) K.metric.toUniformSpace.toTopologicalSpace := by
      letI := K.metric
      infer_instance
    exact (congrArg (fun t : TopologicalSpace (K.G ⧸ K.Γ) =>
      @T2Space (K.G ⧸ K.Γ) t) (nativeNilmanifold_metric_topology K)).mpr hmetric
  letI : BorelSpace (K.G ⧸ K.Γ) := native_nilmanifold_coset_borel K
  exact @native_projected_cube_symmetry_preserves_coset s ℓ J H ρ hρ d (2^d-1)
    (nativeCubeVertexEnumeration d) h (K.G ⧸ K.Γ)
    (QuotientGroup.instTopologicalSpace K.Γ) (by infer_instance)
    (inferInstance : MeasurableSpace (K.G ⧸ K.Γ)) (native_nilmanifold_coset_borel K)
    (nativeFinitePiRestrictedCubeProjection
      (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) index vertex)
    (native_finite_pi_restricted_cube_projection_continuous _ _ _)
    (alignmentJointNativeCosetSlotHomeomorph (D ∘ index) (n ∘ index)
      (fun k => v (index k)) (fun k => hv (index k)) slots)

end Hindman168
