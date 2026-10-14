import Hindman168.AlignmentNativeArrayCharted
import Hindman168.AlignmentNativeArrayTranslations

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

noncomputable def alignmentNativeArrayModelCoefficients :
    alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u ≃ₗ[ℝ]
      alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G) := by
  let f := alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u
  let e := f.equivRangeOfInjective hu
  exact
    { toFun := fun x => e.symm ⟨x.val, x.property⟩
      invFun := fun x => ⟨(e x).val, (e x).property⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact congrArg Subtype.val (e.apply_symm_apply ⟨x.val, x.property⟩)
      right_inv := fun x => e.symm_apply_apply x
      map_add' := fun x y => e.symm.map_add ⟨x.val, x.property⟩ ⟨y.val, y.property⟩
      map_smul' := fun r x => e.symm.map_smul r ⟨x.val, x.property⟩ }

theorem alignmentNativeArrayExponential_evaluation
    (x : alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u) (z : σ → ℤ) :
    (alignmentNativeArrayExponentialHomeomorph n u hu x).val z =
      nativeLieExponential (I := I) (G := G)
        (alignmentLiePolynomialArraysEvaluation (fun j => (z j : ℝ))
          (alignmentNativeArrayModelCoefficients n u hu x)) := by
  letI := nativeFiniteProductSimplyConnected (I := I) (G := G) n
  let f := alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u
  let e := f.equivRangeOfInjective hu
  let c := alignmentNativeArrayModelCoefficients n u hu x
  have hc : f c = x.val := congrArg Subtype.val (e.apply_symm_apply ⟨x.val, x.property⟩)
  have h := alignmentNativeIntegerEvaluation_exponential n u hu z c
  have hp : (⟨nativeLieExponential (I := nativeFiniteProductCorners I n)
      (G := nativeFiniteProduct G n) (f c),
      (alignmentNativeFiniteImageSubgroup_mem_iff (E := E) (I := I) (G := G) n u _).mpr ⟨c, rfl⟩⟩ :
      alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u) =
      nativeLieSubalgebraExponentialHomeomorph (E := nativeFiniteProduct E n) f.range x := by
    apply Subtype.ext
    exact congrArg (nativeLieExponential (I := nativeFiniteProductCorners I n)
      (G := nativeFiniteProduct G n)) hc
  rw [hp] at h
  exact h

noncomputable def alignmentNativeArrayModelTranslation (v : σ → ℤ) :
    alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u →ₗ[ℝ]
      alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u :=
  let e := alignmentNativeArrayModelCoefficients n u hu
  e.symm.toLinearMap.comp ((alignmentLiePolynomialTranslation
    (fun j => (v j : ℝ))).toLinearMap.comp e.toLinearMap)

theorem alignmentNativeArrayTranslation_exponential (v : σ → ℤ)
    (x : alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u) :
    alignmentNativeArrayTranslation n u hu v (alignmentNativeArrayExponentialHomeomorph n u hu x) =
      alignmentNativeArrayExponentialHomeomorph n u hu (alignmentNativeArrayModelTranslation n u hu v x) := by
  apply Subtype.ext
  funext z
  rw [alignmentNativeArrayTranslation_apply, alignmentNativeArrayExponential_evaluation,
    alignmentNativeArrayExponential_evaluation]
  have hc : alignmentNativeArrayModelCoefficients n u hu (alignmentNativeArrayModelTranslation n u hu v x) =
      alignmentLiePolynomialTranslation (fun j => (v j : ℝ)) (alignmentNativeArrayModelCoefficients n u hu x) :=
    (alignmentNativeArrayModelCoefficients n u hu).apply_symm_apply _
  rw [hc, alignmentLiePolynomialTranslation_evaluation]
  congr 3
  funext j
  simp only [Pi.add_apply, Int.cast_add]

end Hindman168

