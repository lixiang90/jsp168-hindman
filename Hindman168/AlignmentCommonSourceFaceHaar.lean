import Hindman168.AlignmentOriginalFaceHaarInvariance
import Hindman168.NativeSequentialCommonPointCubeLimits
import Hindman168.NativeOriginalSequentialFactorization

/-! ONE common-source subsequence discharges the local-law premise in actual
projected face invariance. All fixed positive moduli are controlled BEFORE
its period is chosen. This theorem concerns one fixed target component family. -/
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

theorem alignment_common_source_face_haar
    (F : MasterParameterFamily) (q₀ : ℕ) (T : Finset (Fin N))
    (w : ℕ → ℕ) (y : ℕ → Fin N → ℕ)
    (shift : ℕ → ι → AlignmentAddingPair N i → ℤ) (g a : ∀ _m : ℕ, ∀ ν, (D ν).G)
    (hL : Tendsto (fun m => (alignmentLocalLength F (w m) i : ℝ)) atTop atTop)
    (hgood : ∀ d t : ℕ, 0 < t → ∀ C c B K k : ℕ, ∀ᶠ m in atTop,
      ¬ alignmentNativeCompleteCubeAllFacesFailure (κ := Fin d) D n v hv F q₀ (w m) T t
        (shift m) (g m) (a m) B K (1/(c+1 : ℝ)) C (1/(k+1 : ℝ)) (y m)) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI : MeasurableSpace J.G := borel J.G
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ∃ H : NativeRationalSubgroupFiltration J s,
      (∀ k, H.layer k ≤ (nativeOriginalSubgroupLieFiltration J).layer k) ∧
      ∃ M : ℕ, ∃ hM : 0 < M, ∃ sigma : Fin M → J.G,
      ∃ hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := J.E) (I := J.I) J.Γ,
      ∃ h : ℝ → J.G, ContMDiff 𝓘(ℝ) J.I ∞ h ∧
      NativeResidueLocalHaarLaw J H (fun m => (alignmentLocalLength F (w (f m)) i : ℝ))
        (fun m => alignmentOriginalJointRealSource D n v hv F q₀ (w (f m)) (fun _ => T) (y (f m))
      (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap (w (f m)) i.val) (F.modulus (w (f m))))
        (F.modulus (w (f m))) (y (f m) i)) (shift (f m)) (g (f m)) (a (f m))) M hM sigma hRat h ∧
      NativeCubeBoundedAlphaHaarLaw J H (fun m => (alignmentLocalLength F (w (f m)) i : ℝ))
        (fun m => alignmentOriginalJointRealSource D n v hv F q₀ (w (f m)) (fun _ => T) (y (f m))
      (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap (w (f m)) i.val) (F.modulus (w (f m))))
        (F.modulus (w (f m))) (y (f m) i)) (shift (f m)) (g (f m)) (a (f m))) M hM sigma hRat h ∧
      ∀ (q : Fin (s+2)) (beta : ℝ) (residue : ℤ)
        (weight : ι → Fin q.val → ℤ), (∀ ν j, weight ν j=0 ∨ weight ν j=1) →
        ∀ e : AlignmentAddingPair N i, e.targetTail=T → ∀ j : Fin q.val,
      Measure.map (alignmentJointNativeCosetSlotTranslation D n v hv (fun ν => Pi.single e (weight ν j))) (Measure.map (nativeFinitePiCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) (fun ν => alignmentBinaryCubeVertex (weight ν))) (nativeResidueCubeHaarImage J H (sigma (signedPeriodResidue M hM residue)) (hRat _) q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) (h beta))) =
        Measure.map (nativeFinitePiCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) (fun ν => alignmentBinaryCubeVertex (weight ν))) (nativeResidueCubeHaarImage J H (sigma (signedPeriodResidue M hM residue)) (hRat _) q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) (h beta)) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI : MeasurableSpace J.G := borel J.G
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  let p m := nativeOriginalLeftLinearLog J
    (alignmentOriginalJointPointStep D n v hv (fun _ => T) (y m) (g m))
    (alignmentOriginalJointPointBase D n v hv F q₀ (w m) (fun _ => T) (y m)
      (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap (w m) i.val) (F.modulus (w m)))
        (F.modulus (w m)) (y m i)) (shift m) (g m) (a m))
  obtain ⟨f,hf,hLf,H,hle,M,hM,sigma,hRat,h,hh,hpoint,hreal,hcube,halpha,hcontinuous,hweak,hmixture⟩ :=
    native_sequential_common_point_cube_limits J (nativeOriginalSubgroupLieFiltration J)
      (fun m => (alignmentLocalLength F (w m) i : ℝ)) hL p
      (fun _ => native_original_left_linear_log_weighted J _ _)
  refine ⟨f,hf,H,hle,M,hM,sigma,hRat,h,hh,hpoint,halpha,?_⟩
  intro q beta residue weight hw e he j
  exact alignment_original_face_haar_invariant D n v hv F q₀ T (w ∘ f) (y ∘ f)
    (shift ∘ f) (g ∘ f) (a ∘ f) H M hM sigma hRat h hLf halpha q M hM (dvd_refl _)
    (fun C c B K k => hf.tendsto_atTop.eventually (hgood q.val M hM C c B K k))
    beta residue weight hw e he j

end Hindman168
