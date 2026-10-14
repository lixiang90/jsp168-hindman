import Hindman168.SelectedAlignmentRealStandardCubeComparison
import Hindman168.AlignmentOriginalJointRestriction
import Hindman168.NativeFinitePiRestrictedCubeProjection

/-! Each target's actual empirical comparison is a comparison of a projection
of the SAME full heterogeneous original source. Restriction is used only at
integer sample points, where equality is proved, with unchanged sampling
boxes, normalization, exposure data, and numerical condition budgets. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff BigOperators Classical Topology
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

variable {ι κ : Type} [Fintype ι] [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I)
      (G := (D ν).G) (n ν) (v ν))) (index : κ → ι)

theorem selected_alignment_restricted_real_standard_cube_comparison
    (F : MasterParameterFamily) (gap : Fin N) (q₀ : ℕ) (targets : ι → Finset (Fin N)) (T : Finset (Fin N))
    (hTarget : targets ∘ index = fun _ => T) (d t : ℕ)
    (w : ℕ → ℕ) (y : ℕ → Fin N → ℕ)
    (shift : ℕ → ι → AlignmentAddingPair N i → ℤ) (g a : ∀ _m : ℕ, ∀ ν, (D ν).G)
    (hgood : ∀ C c B K k : ℕ, ∀ᶠ m in atTop,
      ¬ selectedAlignmentNativeCompleteCubeAllFacesFailure (κ := Fin d) (D ∘ index) (n ∘ index) (fun k => v (index k)) (fun k => hv (index k)) F gap q₀ (w m) T t
        ((fun m k => shift m (index k)) m) ((fun m k => g m (index k)) m) ((fun m k => a m (index k)) m) B K (1/(c+1 : ℝ)) C (1/(k+1 : ℝ)) (y m))
    (beta α : ℝ) (hα : 0 < α) (residue : ℤ) :
    let Full := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := Full.metric
    letI : TopologicalSpace (Full.G ⧸ Full.Γ) := Full.metric.toUniformSpace.toTopologicalSpace
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData ((D ∘ index) ν) ((n ∘ index) ν) ((fun k => v (index k)) ν) ((fun k => hv (index k)) ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    ∀ weight : κ → Fin d → ℤ, (∀ ν j, weight ν j=0 ∨ weight ν j=1) →
    ∀ e : AlignmentAddingPair N i, e.targetTail=T → e.sourcePivot < gap → ∀ j : Fin d,
    ∀ obs : C(J.G ⧸ J.Γ,ℂ), ∀ K : NNReal, LipschitzWith K obs →
    Tendsto (fun m =>
      let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap (w m) i.val) (F.modulus (w m)))
        (F.modulus (w m)) (y m i)
      finiteComplexSetMean (alignmentBoxClass (fun z => ⌈cubeAlphaLower d beta (alignmentLocalLength F (w m) i) z⌉) (fun z => ⌈cubeAlphaUpper d beta (alignmentLocalLength F (w m) i) α z⌉) (cubeAlphaResidue d residue) t)
        (fun x => obs (alignmentJointNativeCosetSlotTranslation (D ∘ index) (n ∘ index) (fun k => v (index k)) (fun k => hv (index k))
          (fun ν => Pi.single e (weight ν j)) (nativeFinitePiRestrictedCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) index (fun ν => alignmentBinaryCubeVertex (weight ν)) (fun V => (alignmentOriginalJointRealSource D n v hv F q₀ (w m) targets (y m) p (shift m) (g m) (a m) ((x 0+∑ j ∈ V,x j.succ : ℤ) : ℝ) : Full.G ⧸ Full.Γ))))) -
      finiteComplexSetMean (alignmentBoxClass (fun z => ⌈cubeAlphaLower d beta (alignmentLocalLength F (w m) i) z⌉) (fun z => ⌈cubeAlphaUpper d beta (alignmentLocalLength F (w m) i) α z⌉) (cubeAlphaResidue d residue) t)
        (fun x => obs (nativeFinitePiRestrictedCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) index (fun ν => alignmentBinaryCubeVertex (weight ν)) (fun V => (alignmentOriginalJointRealSource D n v hv F q₀ (w m) targets (y m) p (shift m) (g m) (a m) ((x 0+∑ j ∈ V,x j.succ : ℤ) : ℝ) : Full.G ⧸ Full.Γ))))) atTop (𝓝 0) := by
  dsimp only
  let Full := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData
    (D (index ν)) (n (index ν)) (v (index ν)) (hv (index ν)))
  letI := Full.metric
  letI : TopologicalSpace (Full.G ⧸ Full.Γ) := Full.metric.toUniformSpace.toTopologicalSpace
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  intro weight hw e he hbefore j obs K hK
  simpa only [nativeFinitePiRestrictedCubeProjection,
    alignment_original_joint_real_coset_integer_restriction, hTarget, Function.comp_def] using
    selected_alignment_native_real_standard_cube_comparison (D ∘ index) (n ∘ index)
      (fun k => v (index k)) (fun k => hv (index k)) F gap q₀ T d t w y
      (fun m k => shift m (index k)) (fun m k => g m (index k))
      (fun m k => a m (index k)) hgood beta α hα residue weight hw e he hbefore j obs K hK

end Hindman168
