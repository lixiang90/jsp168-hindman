import Hindman168.AlignmentNativeAllIntegerArrays
import Hindman168.NativeFiniteProductCoordinateTopology

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

noncomputable def alignmentNativeArrayEquiv (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u)) :
    alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u ≃*
      alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu :=
  MonoidHom.ofInjective (alignmentNativeAllIntegerEvaluation_injective n u hu)

theorem alignmentNativeArrayEquiv_symm_coordinate (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (a : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu)
    (i : Fin (n + 1)) :
    nativeFiniteProductCoordinate n ((alignmentNativeArrayEquiv n u hu).symm a).val i =
      a.val (u i) := by
  have h := MonoidHom.apply_ofInjective_symm
    (alignmentNativeAllIntegerEvaluation_injective (E := E) (I := I) (G := G) n u hu) a
  exact (alignmentNativeIntegerEvaluation_selected n u hu _ i).symm.trans (congrFun h (u i))

noncomputable def alignmentNativeArrayHomeomorph (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u)) :
    alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u ≃ₜ
      alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu where
  toEquiv := (alignmentNativeArrayEquiv n u hu).toEquiv
  continuous_toFun := (alignmentNativeAllIntegerEvaluation_continuous n u hu).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (nativeFiniteProduct_continuous_iff n _).mpr
    intro i
    have h : Continuous (fun a : alignmentNativeAllIntegerArrayGroup
        (E := E) (I := I) (G := G) n u hu => a.val (u i)) :=
      (continuous_apply (u i)).comp continuous_subtype_val
    exact h.congr (fun a => (alignmentNativeArrayEquiv_symm_coordinate n u hu a i).symm)

theorem alignmentNativeArrayGroup_contractible (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u)) :
    ContractibleSpace (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) := by
  letI := alignmentNativeFiniteImageSubgroup_contractible (E := E) (I := I) (G := G) n u
  exact (alignmentNativeArrayHomeomorph n u hu).symm.contractibleSpace

theorem alignmentNativeArrayGroup_simplyConnected (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u)) :
    SimplyConnectedSpace (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) := by
  letI := alignmentNativeArrayGroup_contractible (E := E) (I := I) (G := G) n u hu
  infer_instance

end Hindman168

