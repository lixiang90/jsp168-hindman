import Hindman168.AlignmentNativeArrayCharted

namespace Hindman168
open scoped Manifold ContDiff

attribute [local instance 10] nativeFiniteProductTopologicalSpace
attribute [local instance] nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three

variable {σ : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [ConnectedSpace G] [SimplyConnectedSpace G]

variable (n : ℕ) (u : Fin (n + 1) → σ → ℤ)
  (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))

theorem alignmentNativeArrayDiffeomorph_symm_apply
    (a : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) :
    letI := alignmentNativeFiniteImageChartedSpace (E := E) (I := I) (G := G) n u
    letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
    (alignmentNativeArrayDiffeomorph n u hu).symm a = (alignmentNativeArrayEquiv n u hu).symm a := by
  letI := alignmentNativeFiniteImageChartedSpace (E := E) (I := I) (G := G) n u
  letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
  apply (alignmentNativeArrayEquiv n u hu).injective
  rw [MulEquiv.apply_symm_apply]
  exact (alignmentNativeArrayDiffeomorph_apply n u hu _).symm.trans
    ((alignmentNativeArrayDiffeomorph n u hu).apply_symm_apply a)

theorem alignmentNativeArrayEquiv_contMDiff :
    letI := alignmentNativeFiniteImageChartedSpace (E := E) (I := I) (G := G) n u
    letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
    let J := 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u)
    ContMDiff J J ∞ (alignmentNativeArrayEquiv n u hu) := by
  letI := alignmentNativeFiniteImageChartedSpace (E := E) (I := I) (G := G) n u
  letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
  exact (alignmentNativeArrayDiffeomorph n u hu).contMDiff_toFun.congr
    (fun g => (alignmentNativeArrayDiffeomorph_apply n u hu g).symm)

theorem alignmentNativeArrayEquiv_symm_contMDiff :
    letI := alignmentNativeFiniteImageChartedSpace (E := E) (I := I) (G := G) n u
    letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
    let J := 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u)
    ContMDiff J J ∞ (alignmentNativeArrayEquiv n u hu).symm := by
  letI := alignmentNativeFiniteImageChartedSpace (E := E) (I := I) (G := G) n u
  letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
  exact (alignmentNativeArrayDiffeomorph n u hu).contMDiff_invFun.congr
    (fun a => (alignmentNativeArrayDiffeomorph_symm_apply n u hu a).symm)

theorem alignmentNativeArray_lieGroup :
    letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
    LieGroup 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u) ∞
      (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) := by
  letI := alignmentNativeFiniteImageChartedSpace (E := E) (I := I) (G := G) n u
  letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
  letI := alignmentNativeFiniteImage_lieGroup (E := E) (I := I) (G := G) n u
  letI := alignmentNativeArray_isManifold n u hu
  let J := 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u)
  let A := alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu
  let e := alignmentNativeArrayEquiv (E := E) (I := I) (G := G) n u hu
  have he := alignmentNativeArrayEquiv_contMDiff n u hu
  have hi := alignmentNativeArrayEquiv_symm_contMDiff n u hu
  refine { contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · have h1 : ContMDiff (J.prod J) J ∞ (fun p : A × A => e.symm p.1) := hi.comp contMDiff_fst
    have h2 : ContMDiff (J.prod J) J ∞ (fun p : A × A => e.symm p.2) := hi.comp contMDiff_snd
    exact (he.comp (h1.mul h2)).congr (fun p => by
      change p.1 * p.2 = e (e.symm p.1 * e.symm p.2)
      rw [map_mul, e.apply_symm_apply, e.apply_symm_apply])
  · exact (he.comp hi.inv).congr (fun a => by
      change a⁻¹ = e (e.symm a)⁻¹
      rw [map_inv, e.apply_symm_apply])

theorem alignmentNativeArray_boundaryless :
    letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
    BoundarylessManifold 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u)
      (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) := by
  letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
  infer_instance

theorem alignmentNativeArray_evaluation_contMDiff (z : σ → ℤ) :
    letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
    ContMDiff 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u) I ∞
      (fun a : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu => a.val z) := by
  letI := alignmentNativeFiniteImageChartedSpace (E := E) (I := I) (G := G) n u
  letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
  have h := (alignmentNativeIntegerEvaluation_contMDiff n u hu z).comp
    (alignmentNativeArrayEquiv_symm_contMDiff n u hu)
  exact h.congr (fun a => (congrFun (MonoidHom.apply_ofInjective_symm
    (alignmentNativeAllIntegerEvaluation_injective (E := E) (I := I) (G := G) n u hu) a) z).symm)

end Hindman168

