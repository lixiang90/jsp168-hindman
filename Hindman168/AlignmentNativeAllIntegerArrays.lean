import Hindman168.AlignmentNativeIntegerEvaluation

/-! All integer evaluations simultaneously form a faithful group map
into actual pointwise arrays. Its range is exactly the exponential
arrays of the genuine graded coefficient algebra, independently of the
chosen finite determining evaluation family. -/

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

noncomputable def alignmentNativeAllIntegerEvaluation (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u)) :
    alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u →* ((σ → ℤ) → G) where
  toFun g z := alignmentNativeIntegerEvaluation (E := E) (I := I) (G := G) n u hu z g
  map_one' := funext fun z => map_one (alignmentNativeIntegerEvaluation (E := E) (I := I) (G := G) n u hu z)
  map_mul' g h := funext fun z => map_mul (alignmentNativeIntegerEvaluation (E := E) (I := I) (G := G) n u hu z) g h

theorem alignmentNativeAllIntegerEvaluation_continuous (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u)) :
    Continuous (alignmentNativeAllIntegerEvaluation (E := E) (I := I) (G := G) n u hu) :=
  continuous_pi fun z => alignmentNativeIntegerEvaluation_continuous n u hu z

theorem alignmentNativeAllIntegerEvaluation_injective (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u)) :
    Function.Injective (alignmentNativeAllIntegerEvaluation (E := E) (I := I) (G := G) n u hu) := by
  intro g h hgh
  apply Subtype.ext
  apply nativeFiniteProductCoordinate_injective n
  funext i
  exact (alignmentNativeIntegerEvaluation_selected n u hu g i).symm.trans
    ((congrFun hgh (u i)).trans (alignmentNativeIntegerEvaluation_selected n u hu h i))

noncomputable def alignmentNativeAllIntegerArrayGroup (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u)) :
    Subgroup ((σ → ℤ) → G) :=
  (alignmentNativeAllIntegerEvaluation (E := E) (I := I) (G := G) n u hu).range

theorem alignmentNativeAllIntegerArrayGroup_mem_iff (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (a : (σ → ℤ) → G) :
    a ∈ alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ↔
      ∃ x : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G),
        ∀ z : σ → ℤ, nativeLieExponential (I := I) (G := G)
          (alignmentLiePolynomialArraysEvaluation (fun j => (z j : ℝ)) x) = a z := by
  change (∃ g : alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u,
    alignmentNativeAllIntegerEvaluation (E := E) (I := I) (G := G) n u hu g = a) ↔ _
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨x, hx⟩ := (alignmentNativeFiniteImageSubgroup_mem_iff (E := E)
      (I := I) (G := G) n u g.val).mp g.property
    let p : alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u :=
      ⟨nativeLieExponential (I := nativeFiniteProductCorners I n) (G := nativeFiniteProduct G n)
        (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u x),
        (alignmentNativeFiniteImageSubgroup_mem_iff (E := E) (I := I) (G := G) n u _).mpr ⟨x, rfl⟩⟩
    have hp : p = g := Subtype.ext hx
    refine ⟨x, fun z => ?_⟩
    exact (alignmentNativeIntegerEvaluation_exponential n u hu z x).symm.trans
      ((congrArg (alignmentNativeIntegerEvaluation (E := E) (I := I) (G := G) n u hu z) hp).trans
        (congrFun hg z))
  · rintro ⟨x, hx⟩
    refine ⟨⟨nativeLieExponential (I := nativeFiniteProductCorners I n) (G := nativeFiniteProduct G n)
      (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u x),
      (alignmentNativeFiniteImageSubgroup_mem_iff (E := E) (I := I) (G := G) n u _).mpr ⟨x, rfl⟩⟩, ?_⟩
    funext z
    exact (alignmentNativeIntegerEvaluation_exponential n u hu z x).trans (hx z)

theorem alignmentNativeIntegerExponentialArray_injective (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u)) :
    Function.Injective (fun x : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G) =>
      fun z : σ → ℤ => nativeLieExponential (I := I) (G := G)
        (alignmentLiePolynomialArraysEvaluation (fun j => (z j : ℝ)) x)) := by
  intro x y hxy
  apply alignmentNativeFiniteImageExponential_injective n u hu
  apply nativeFiniteProductCoordinate_injective n
  funext i
  exact (alignmentNativeFiniteImageSubgroup_coordinate n u x i).trans
    ((congrFun hxy (u i)).trans (alignmentNativeFiniteImageSubgroup_coordinate n u y i).symm)

theorem alignmentNativeAllIntegerArrayGroup_independent (n m : ℕ)
    (u : Fin (n + 1) → σ → ℤ) (v : Fin (m + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (hv : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) m v)) :
    alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu =
      alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) m v hv := by
  ext a
  rw [alignmentNativeAllIntegerArrayGroup_mem_iff, alignmentNativeAllIntegerArrayGroup_mem_iff]

end Hindman168
