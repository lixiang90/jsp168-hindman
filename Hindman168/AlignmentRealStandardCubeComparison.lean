import Hindman168.AlignmentNativeStandardCubeComparison
import Hindman168.AlignmentOriginalJointRealSource

/-! The actual countable good-condition budgets imply projected comparison
on every fixed standard alpha window and every fixed Lipschitz test. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff BigOperators Classical Topology
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

variable {ι : Type} [Fintype ι] 
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

theorem alignment_native_real_standard_cube_comparison
    (F : MasterParameterFamily) (q₀ : ℕ) (T : Finset (Fin N)) (d t : ℕ)
    (w : ℕ → ℕ) (y : ℕ → Fin N → ℕ)
    (shift : ℕ → ι → AlignmentAddingPair N i → ℤ) (g a : ∀ _m : ℕ, ∀ ν, (D ν).G)
    (hgood : ∀ C c B K k : ℕ, ∀ᶠ m in atTop,
      ¬ alignmentNativeCompleteCubeAllFacesFailure (κ := Fin d) D n v hv F q₀ (w m) T t
        (shift m) (g m) (a m) B K (1/(c+1 : ℝ)) C (1/(k+1 : ℝ)) (y m))
    (beta α : ℝ) (hα : 0 < α) (residue : ℤ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    ∀ weight : ι → Fin d → ℤ, (∀ ν j, weight ν j=0 ∨ weight ν j=1) →
    ∀ e : AlignmentAddingPair N i, e.targetTail=T → ∀ j : Fin d,
    ∀ obs : C(J.G ⧸ J.Γ,ℂ), ∀ K : NNReal, LipschitzWith K obs →
    Tendsto (fun m =>
      let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap (w m) i.val) (F.modulus (w m)))
        (F.modulus (w m)) (y m i)
      finiteComplexSetMean (alignmentBoxClass (fun z => ⌈cubeAlphaLower d beta (alignmentLocalLength F (w m) i) z⌉) (fun z => ⌈cubeAlphaUpper d beta (alignmentLocalLength F (w m) i) α z⌉) (cubeAlphaResidue d residue) t)
        (fun x => obs (alignmentJointNativeCosetSlotTranslation D n v hv
          (fun ν => Pi.single e (weight ν j)) (nativeFinitePiCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) (fun ν => alignmentBinaryCubeVertex (weight ν)) (fun V => (alignmentOriginalJointRealSource D n v hv F q₀ (w m) (fun _ => T) (y m) p (shift m) (g m) (a m) ((x 0+∑ j ∈ V,x j.succ : ℤ) : ℝ) : J.G ⧸ J.Γ))))) -
      finiteComplexSetMean (alignmentBoxClass (fun z => ⌈cubeAlphaLower d beta (alignmentLocalLength F (w m) i) z⌉) (fun z => ⌈cubeAlphaUpper d beta (alignmentLocalLength F (w m) i) α z⌉) (cubeAlphaResidue d residue) t)
        (fun x => obs (nativeFinitePiCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) (fun ν => alignmentBinaryCubeVertex (weight ν)) (fun V => (alignmentOriginalJointRealSource D n v hv F q₀ (w m) (fun _ => T) (y m) p (shift m) (g m) (a m) ((x 0+∑ j ∈ V,x j.succ : ℤ) : ℝ) : J.G ⧸ J.Γ))))) atTop (𝓝 0) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  intro weight hw e he j obs K hK
  simpa only [alignment_original_joint_real_source_integer] using
    alignment_native_standard_cube_comparison D n v hv F q₀ T d t w y shift g a hgood
      beta α hα residue weight hw e he j obs K hK

end Hindman168
