import Hindman168.AlignmentNativeAllIntegerArrays
import Hindman168.AlignmentLiePolynomialTranslation
import Hindman168.AlignmentArrayInputTranslations

namespace Hindman168
open scoped Manifold ContDiff

attribute [local instance] nativeFiniteProductTopologicalSpace nativeFiniteProductGroup
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

theorem alignmentNativeArrayTranslation_mem (v : σ → ℤ)
    (a : (σ → ℤ) → G)
    (ha : a ∈ alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) :
    alignmentArrayInputTranslation v a ∈
      alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu := by
  obtain ⟨x, hx⟩ := (alignmentNativeAllIntegerArrayGroup_mem_iff n u hu a).mp ha
  apply (alignmentNativeAllIntegerArrayGroup_mem_iff n u hu _).mpr
  refine ⟨alignmentLiePolynomialTranslation (fun j => (v j : ℝ)) x, fun z => ?_⟩
  rw [alignmentLiePolynomialTranslation_evaluation]
  have h : (fun j => (z j : ℝ)) + (fun j => (v j : ℝ)) =
      (fun j => ((z + v) j : ℝ)) := by
    funext j
    simp only [Pi.add_apply, Int.cast_add]
  rw [h]
  exact hx (z + v)

noncomputable def alignmentNativeArrayTranslation (v : σ → ℤ) :
    alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ≃*
      alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu where
  toFun a := ⟨alignmentArrayInputTranslation v a.val,
    alignmentNativeArrayTranslation_mem n u hu v a.val a.property⟩
  invFun a := ⟨alignmentArrayInputTranslation (-v) a.val,
    alignmentNativeArrayTranslation_mem n u hu (-v) a.val a.property⟩
  left_inv a := by
    apply Subtype.ext
    funext z
    change a.val ((z + -v) + v) = a.val z
    rw [neg_add_cancel_right]
  right_inv a := by
    apply Subtype.ext
    funext z
    change a.val ((z + v) + -v) = a.val z
    rw [add_neg_cancel_right]
  map_mul' _ _ := rfl

theorem alignmentNativeArrayTranslation_apply (v z : σ → ℤ)
    (a : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) :
    (alignmentNativeArrayTranslation n u hu v a).val z = a.val (z + v) := rfl

theorem alignmentNativeArrayTranslation_add (v w : σ → ℤ)
    (a : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) :
    alignmentNativeArrayTranslation n u hu v (alignmentNativeArrayTranslation n u hu w a) =
      alignmentNativeArrayTranslation n u hu (v + w) a := by
  apply Subtype.ext
  funext z
  change a.val ((z + v) + w) = a.val (z + (v + w))
  rw [add_assoc]

theorem alignmentNativeArrayTranslation_continuous (v : σ → ℤ) :
    Continuous (alignmentNativeArrayTranslation (E := E) (I := I) (G := G) n u hu v) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro z
  exact (continuous_apply (z + v)).comp continuous_subtype_val

noncomputable def alignmentNativeArrayTranslationHomeomorph (v : σ → ℤ) :
    alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ≃ₜ
      alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu where
  __ := (alignmentNativeArrayTranslation (E := E) (I := I) (G := G) n u hu v).toEquiv
  continuous_toFun := alignmentNativeArrayTranslation_continuous n u hu v
  continuous_invFun := alignmentNativeArrayTranslation_continuous n u hu (-v)

end Hindman168
