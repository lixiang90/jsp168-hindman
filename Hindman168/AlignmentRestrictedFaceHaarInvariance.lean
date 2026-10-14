import Hindman168.AlignmentRestrictedCubeHaarInvariant
import Hindman168.AlignmentRestrictedRealCubeComparison
import Hindman168.NativeProjectedCubeEmpiricalInvariance

/-! The empirical comparisons for a target subfamily yield invariance of
its projection of the SAME full heterogeneous joint Haar measure. The local
law is for the full original source, never a separately selected target law.
This is the transfer step; a subsequent common-source extraction discharges
the full local-law premise. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Manifold ContDiff BigOperators Classical Topology
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

variable {ι κ : Type} [Fintype ι] [Fintype κ] 
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν))) (index : κ → ι)

theorem alignment_restricted_face_haar_invariant
    (F : MasterParameterFamily) (q₀ : ℕ) (targets : ι → Finset (Fin N)) (T : Finset (Fin N))
    (hTarget : targets ∘ index = fun _ => T)
    (w : ℕ → ℕ) (y : ℕ → Fin N → ℕ)
    (shift : ℕ → ι → AlignmentAddingPair N i → ℤ) (g a : ∀ _m : ℕ, ∀ ν, (D ν).G)
    {ℓ : ℕ} (H : NativeRationalSubgroupFiltration (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) ℓ)
    (M : ℕ) (hM : 0 < M) (sigma : Fin M → (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).E) (I := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).I) (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ)
    (h : ℝ → (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
    (hL : Tendsto (fun m => (alignmentLocalLength F (w m) i : ℝ)) atTop atTop)
    (hlaw : NativeCubeBoundedAlphaHaarLaw (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) H (fun m => (alignmentLocalLength F (w m) i : ℝ))
      (fun m z => alignmentOriginalJointRealSource D n v hv F q₀ (w m) targets (y m) (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap (w m) i.val) (F.modulus (w m))) (F.modulus (w m)) (y m i)) (shift m) (g m) (a m) z) M hM sigma hRat h)
    (q : Fin (s+2)) (t : ℕ) (ht : 0 < t) (hMt : (M : ℤ) ∣ (t : ℤ))
    (hgood : ∀ C c B K k : ℕ, ∀ᶠ m in atTop,
      ¬ alignmentNativeCompleteCubeAllFacesFailure (κ := Fin q.val) (D ∘ index) (n ∘ index) (fun k => v (index k)) (fun k => hv (index k)) F q₀ (w m) T t
        (fun k => shift m (index k)) (fun k => g m (index k)) (fun k => a m (index k)) B K (1/(c+1 : ℝ)) C (1/(k+1 : ℝ)) (y m))
    (beta : ℝ) (residue : ℤ)
    (weight : κ → Fin q.val → ℤ) (hw : ∀ ν j, weight ν j=0 ∨ weight ν j=1)
    (e : AlignmentAddingPair N i) (he : e.targetTail=T) (j : Fin q.val) :
    AlignmentRestrictedCubeHaarInvariant D n v hv index H
      (sigma (signedPeriodResidue M hM residue)) (hRat _) q.val (h beta)
      (fun ν => alignmentBinaryCubeVertex (weight ν)) (fun ν => Pi.single e (weight ν j)) := by
  unfold AlignmentRestrictedCubeHaarInvariant
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI : MeasurableSpace J.G := borel J.G
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  let K := nativeFinitePiData (fun k => alignmentNativeArrayData
    (D (index k)) (n (index k)) (v (index k)) (hv (index k)))
  letI : MeasurableSpace K.G := borel K.G
  letI := K.metric
  letI : TopologicalSpace (K.G ⧸ K.Γ) := K.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (K.G ⧸ K.Γ) := native_nilmanifold_metric_quotient_compact K
  letI : BorelSpace (K.G ⧸ K.Γ) := native_nilmanifold_metric_coset_borel K
  let π : C((Finset (Fin q.val) → J.G ⧸ J.Γ),K.G ⧸ K.Γ) :=
    ⟨nativeFinitePiRestrictedCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) index (fun ν => alignmentBinaryCubeVertex (weight ν)),native_finite_pi_metric_restricted_cube_projection_continuous _ _ _⟩
  exact native_projected_cube_empirical_invariance (Y := K.G ⧸ K.Γ) J H (fun m => (alignmentLocalLength F (w m) i : ℝ)) (fun m z => alignmentOriginalJointRealSource D n v hv F q₀ (w m) targets (y m) (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap (w m) i.val) (F.modulus (w m))) (F.modulus (w m)) (y m i)) (shift m) (g m) (a m) z)
    M hM sigma hRat h hL hlaw q beta t ht hMt residue π (alignmentJointNativeCosetSlotTranslation (D ∘ index) (n ∘ index) (fun k => v (index k)) (fun k => hv (index k)) (fun ν => Pi.single e (weight ν j)))
    (alignment_joint_native_metric_coset_slot_translation_continuous (D ∘ index) (n ∘ index) (fun k => v (index k)) (fun k => hv (index k)) _)
    (fun α hα obs K hK => alignment_restricted_real_standard_cube_comparison D n v hv index F q₀ targets T hTarget q.val t w y
      shift g a hgood beta α hα residue weight hw e he j obs K hK)

end Hindman168
