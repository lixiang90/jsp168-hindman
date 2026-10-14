import Hindman168.SelectedAlignmentNativeProjectedCubeConvergence
import Hindman168.CubeOptionWindowMean
import Hindman168.CubeStandardWindowBudgets

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

theorem selected_alignment_native_standard_cube_comparison
    (F : MasterParameterFamily) (gap : Fin N) (q₀ : ℕ) (T : Finset (Fin N)) (d t : ℕ)
    (w : ℕ → ℕ) (y : ℕ → Fin N → ℕ)
    (shift : ℕ → ι → AlignmentAddingPair N i → ℤ) (g a : ∀ _m : ℕ, ∀ ν, (D ν).G)
    (hgood : ∀ C c B K k : ℕ, ∀ᶠ m in atTop,
      ¬ selectedAlignmentNativeCompleteCubeAllFacesFailure (κ := Fin d) D n v hv F gap q₀ (w m) T t
        (shift m) (g m) (a m) B K (1/(c+1 : ℝ)) C (1/(k+1 : ℝ)) (y m))
    (beta α : ℝ) (hα : 0 < α) (residue : ℤ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    ∀ weight : ι → Fin d → ℤ, (∀ ν j, weight ν j=0 ∨ weight ν j=1) →
    ∀ e : AlignmentAddingPair N i, e.targetTail=T → e.sourcePivot < gap → ∀ j : Fin d,
    ∀ obs : C(J.G ⧸ J.Γ,ℂ), ∀ K : NNReal, LipschitzWith K obs →
    Tendsto (fun m =>
      let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap (w m) i.val) (F.modulus (w m)))
        (F.modulus (w m)) (y m i)
      finiteComplexSetMean (alignmentBoxClass (fun z => ⌈cubeAlphaLower d beta (alignmentLocalLength F (w m) i) z⌉) (fun z => ⌈cubeAlphaUpper d beta (alignmentLocalLength F (w m) i) α z⌉) (cubeAlphaResidue d residue) t)
        (fun x => obs (alignmentJointNativeCosetSlotTranslation D n v hv
          (fun ν => Pi.single e (weight ν j)) (nativeFinitePiCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) (fun ν => alignmentBinaryCubeVertex (weight ν)) (fun V => (alignmentOriginalJointPointOrbit D n v hv F q₀ (w m) (fun _ => T) (y m) p (shift m) (g m) (a m) (x 0+∑ j ∈ V,x j.succ) : J.G ⧸ J.Γ))))) -
      finiteComplexSetMean (alignmentBoxClass (fun z => ⌈cubeAlphaLower d beta (alignmentLocalLength F (w m) i) z⌉) (fun z => ⌈cubeAlphaUpper d beta (alignmentLocalLength F (w m) i) α z⌉) (cubeAlphaResidue d residue) t)
        (fun x => obs (nativeFinitePiCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) (fun ν => alignmentBinaryCubeVertex (weight ν)) (fun V => (alignmentOriginalJointPointOrbit D n v hv F q₀ (w m) (fun _ => T) (y m) p (shift m) (g m) (a m) (x 0+∑ j ∈ V,x j.succ) : J.G ⧸ J.Γ))))) atTop (𝓝 0) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
  intro weight hw e he hbefore j obs K hK
  obtain ⟨C,c,hgeom⟩ := cube_standard_window_integer_budgets d beta α hα
  obtain ⟨B,hB⟩ := exists_nat_gt ‖obs‖
  obtain ⟨Knat,hKn⟩ := exists_nat_gt (K : ℝ)
  have hKL : K ≤ (Knat : NNReal) := by exact_mod_cast hKn.le
  have hobs : obs ∈ boundedComplexLipschitzObservables (J.G ⧸ J.Γ) B Knat :=
    ⟨hK.weaken hKL,fun z => (obs.norm_coe_le_norm z).trans hB.le⟩
  have hcomp := selected_alignment_native_good_projected_cube_means_tendsto D n v hv F gap q₀ T t w y shift g a
    B Knat (1/(c+1 : ℝ)) C (hgood C c B Knat) weight hw e he hbefore j
    (fun m z => cubeAlphaLower d beta (alignmentLocalLength F (w m) i) ((finSuccEquiv d).symm z))
    (fun m z => cubeAlphaUpper d beta (alignmentLocalLength F (w m) i) α ((finSuccEquiv d).symm z))
    (fun _ z => cubeAlphaResidue d residue ((finSuccEquiv d).symm z)) obs
    (Eventually.of_forall (fun m z => hgeom _ (Nat.cast_nonneg _) ((finSuccEquiv d).symm z))) hobs
  convert hcomp using 1
  funext m
  dsimp only
  let p0 := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap (w m) i.val) (F.modulus (w m)))
    (F.modulus (w m)) (y m i)
  let O : ℤ → J.G ⧸ J.Γ := fun z =>
    (alignmentOriginalJointPointOrbit D n v hv F q₀ (w m) (fun _ => T) (y m) p0
      (shift m) (g m) (a m) z : J.G ⧸ J.Γ)
  let project := nativeFinitePiCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    (fun ν => alignmentBinaryCubeVertex (weight ν))
  have h1 := cube_option_standard_window_mean d beta (alignmentLocalLength F (w m) i) α residue t O
    (fun x => obs (alignmentJointNativeCosetSlotTranslation D n v hv (fun ν => Pi.single e (weight ν j)) (project x)))
  have h2 := cube_option_standard_window_mean d beta (alignmentLocalLength F (w m) i) α residue t O
    (fun x => obs (project x))
  exact congrArg₂ (fun z z' : ℂ => z-z') h1.symm h2.symm

end Hindman168
