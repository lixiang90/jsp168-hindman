import Hindman168.AlignmentOriginalJointRestriction
import Hindman168.AlignmentRealStandardCubeComparison

/-! A target subfamily's actual comparison is comparison of a projection of
the FULL heterogeneous original cube source. No target source is substituted. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff BigOperators Classical Topology
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

variable {ι κ : Type} [Fintype ι] [Fintype κ] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

theorem alignment_restricted_real_cube_comparison (select : κ → ι)
    (F : MasterParameterFamily) (q₀ : ℕ) (targets : ι → Finset (Fin N)) (T : Finset (Fin N))
    (hT : ∀ k, targets (select k)=T) (d t : ℕ)
    (w : ℕ → ℕ) (y : ℕ → Fin N → ℕ)
    (shift : ℕ → ι → AlignmentAddingPair N i → ℤ) (g a : ∀ _m : ℕ, ∀ ν, (D ν).G)
    (hgood : ∀ C c B K k : ℕ, ∀ᶠ m in atTop,
      ¬ alignmentNativeCompleteCubeAllFacesFailure (κ := Fin d) (D ∘ select) (n ∘ select) (fun k => v (select k)) (fun k => hv (select k)) F q₀ (w m) T t
        (fun k => shift m (select k)) (fun k => g m (select k)) (fun k => a m (select k))
        B K (1/(c+1 : ℝ)) C (1/(k+1 : ℝ)) (y m))
    (beta α : ℝ) (hα : 0 < α) (residue : ℤ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    let R := nativeFinitePiData ((fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) ∘ select)
    letI := R.metric
    letI : TopologicalSpace (R.G ⧸ R.Γ) := R.metric.toUniformSpace.toTopologicalSpace
    ∀ weight : κ → Fin d → ℤ, (∀ k j, weight k j=0 ∨ weight k j=1) →
    ∀ e : AlignmentAddingPair N i, e.targetTail=T → ∀ j : Fin d,
    ∀ obs : C(R.G ⧸ R.Γ,ℂ), ∀ K : NNReal, LipschitzWith K obs →
    Tendsto (fun m =>
      let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap (w m) i.val) (F.modulus (w m)))
        (F.modulus (w m)) (y m i)
      finiteComplexSetMean (alignmentBoxClass (fun z => ⌈cubeAlphaLower d beta (alignmentLocalLength F (w m) i) z⌉) (fun z => ⌈cubeAlphaUpper d beta (alignmentLocalLength F (w m) i) α z⌉) (cubeAlphaResidue d residue) t)
        (fun x => obs (alignmentJointNativeCosetSlotTranslation (D ∘ select) (n ∘ select) (fun k => v (select k)) (fun k => hv (select k))
          (fun k => Pi.single e (weight k j)) (nativeFinitePiRestrictedCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) select (fun k => alignmentBinaryCubeVertex (weight k)) (fun V => (alignmentOriginalJointRealSource D n v hv F q₀ (w m) targets (y m) p (shift m) (g m) (a m) ((x 0+∑ j ∈ V,x j.succ : ℤ) : ℝ) : J.G ⧸ J.Γ))))) -
      finiteComplexSetMean (alignmentBoxClass (fun z => ⌈cubeAlphaLower d beta (alignmentLocalLength F (w m) i) z⌉) (fun z => ⌈cubeAlphaUpper d beta (alignmentLocalLength F (w m) i) α z⌉) (cubeAlphaResidue d residue) t)
        (fun x => obs (nativeFinitePiRestrictedCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) select (fun k => alignmentBinaryCubeVertex (weight k)) (fun V => (alignmentOriginalJointRealSource D n v hv F q₀ (w m) targets (y m) p (shift m) (g m) (a m) ((x 0+∑ j ∈ V,x j.succ : ℤ) : ℝ) : J.G ⧸ J.Γ))))) atTop (𝓝 0) := by
  dsimp only
  let R := nativeFinitePiData ((fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) ∘ select)
  letI := R.metric
  letI : TopologicalSpace (R.G ⧸ R.Γ) := R.metric.toUniformSpace.toTopologicalSpace
  intro weight hw e he j obs K hK
  have htargets : targets ∘ select = fun _ => T := funext hT
  have hlocal := alignment_native_real_standard_cube_comparison (D ∘ select) (n ∘ select) (fun k => v (select k)) (fun k => hv (select k)) F q₀ T d t w y
    (fun m k => shift m (select k)) (fun m k => g m (select k)) (fun m k => a m (select k))
    hgood beta α hα residue weight hw e he j obs K hK
  simpa only [nativeFinitePiRestrictedCubeProjection,alignment_original_joint_real_restriction_integer,htargets] using hlocal

end Hindman168
