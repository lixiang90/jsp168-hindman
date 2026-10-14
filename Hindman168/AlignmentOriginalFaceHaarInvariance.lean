import Hindman168.AlignmentRealStandardCubeComparison
import Hindman168.NativeProjectedCubeEmpiricalInvariance

/-! Actual good-condition comparison plus the local Haar law of the SAME
original source proves projected face Haar invariance. The local law must
still be obtained on the selected common source, not postulated externally. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Manifold ContDiff BigOperators Classical Topology
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

variable {ι : Type} [Fintype ι] 
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

theorem alignment_original_face_haar_invariant
    (F : MasterParameterFamily) (q₀ : ℕ) (T : Finset (Fin N))
    (w : ℕ → ℕ) (y : ℕ → Fin N → ℕ)
    (shift : ℕ → ι → AlignmentAddingPair N i → ℤ) (g a : ∀ _m : ℕ, ∀ ν, (D ν).G)
    {ℓ : ℕ} (H : NativeRationalSubgroupFiltration (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) ℓ)
    (M : ℕ) (hM : 0 < M) (sigma : Fin M → (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).E) (I := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).I) (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ)
    (h : ℝ → (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
    (hL : Tendsto (fun m => (alignmentLocalLength F (w m) i : ℝ)) atTop atTop)
    (hlaw : NativeCubeBoundedAlphaHaarLaw (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) H (fun m => (alignmentLocalLength F (w m) i : ℝ))
      (fun m z => alignmentOriginalJointRealSource D n v hv F q₀ (w m) (fun _ => T) (y m) (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap (w m) i.val) (F.modulus (w m))) (F.modulus (w m)) (y m i)) (shift m) (g m) (a m) z) M hM sigma hRat h)
    (q : Fin (s+2)) (t : ℕ) (ht : 0 < t) (hMt : (M : ℤ) ∣ (t : ℤ))
    (hgood : ∀ C c B K k : ℕ, ∀ᶠ m in atTop,
      ¬ alignmentNativeCompleteCubeAllFacesFailure (κ := Fin q.val) D n v hv F q₀ (w m) T t
        (shift m) (g m) (a m) B K (1/(c+1 : ℝ)) C (1/(k+1 : ℝ)) (y m))
    (beta : ℝ) (residue : ℤ)
    (weight : ι → Fin q.val → ℤ) (hw : ∀ ν j, weight ν j=0 ∨ weight ν j=1)
    (e : AlignmentAddingPair N i) (he : e.targetTail=T) (j : Fin q.val) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI : MeasurableSpace J.G := borel J.G
    Measure.map (alignmentJointNativeCosetSlotTranslation D n v hv (fun ν => Pi.single e (weight ν j))) (Measure.map (nativeFinitePiCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) (fun ν => alignmentBinaryCubeVertex (weight ν))) (nativeResidueCubeHaarImage J H (sigma (signedPeriodResidue M hM residue)) (hRat _) q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) (h beta))) =
      Measure.map (nativeFinitePiCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) (fun ν => alignmentBinaryCubeVertex (weight ν))) (nativeResidueCubeHaarImage J H (sigma (signedPeriodResidue M hM residue)) (hRat _) q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) (h beta)) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI : MeasurableSpace J.G := borel J.G
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (J.G ⧸ J.Γ) := native_nilmanifold_metric_quotient_compact J
  letI : BorelSpace (J.G ⧸ J.Γ) := native_nilmanifold_metric_coset_borel J
  let π : C((Finset (Fin q.val) → J.G ⧸ J.Γ),J.G ⧸ J.Γ) :=
    ⟨nativeFinitePiCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) (fun ν => alignmentBinaryCubeVertex (weight ν)),native_finite_pi_metric_cube_projection_continuous _ _⟩
  exact native_projected_cube_empirical_invariance J H (fun m => (alignmentLocalLength F (w m) i : ℝ)) (fun m z => alignmentOriginalJointRealSource D n v hv F q₀ (w m) (fun _ => T) (y m) (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap (w m) i.val) (F.modulus (w m))) (F.modulus (w m)) (y m i)) (shift m) (g m) (a m) z)
    M hM sigma hRat h hL hlaw q beta t ht hMt residue π (alignmentJointNativeCosetSlotTranslation D n v hv (fun ν => Pi.single e (weight ν j)))
    (alignment_joint_native_metric_coset_slot_translation_continuous D n v hv _)
    (fun α hα obs K hK => alignment_native_real_standard_cube_comparison D n v hv F q₀ T q.val t w y
      shift g a hgood beta α hα residue weight hw e he j obs K hK)

end Hindman168
