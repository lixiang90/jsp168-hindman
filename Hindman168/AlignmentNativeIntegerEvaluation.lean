import Hindman168.NativeLieSubalgebraIntegrationContinuity
import Hindman168.AlignmentNativeFiniteImageSubgroup

/-! Every additional integer input induces an actual continuous group
evaluation on the integrated finite image, by genuine graph integration. -/

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

noncomputable def alignmentNativeIntegerEvaluation (n : ℕ) (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (z : σ → ℤ) : alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u →* G := by
  letI := nativeFiniteProductSimplyConnected (I := I) (G := G) n
  let f := alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u
  let φ := (alignmentLiePolynomialArraysEvaluation (L := GroupLieAlgebra I G)
    (fun j => (z j : ℝ))).comp (f.equivRangeOfInjective hu).symm.toLieHom
  exact nativeLieSubalgebraIntegrate (E := nativeFiniteProduct E n) (F := E)
    (I := nativeFiniteProductCorners I n) (J := I) (G := nativeFiniteProduct G n) (K := G)
    f.range φ

theorem alignmentNativeIntegerEvaluation_exponential (n : ℕ) (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (z : σ → ℤ) (x : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G)) :
    alignmentNativeIntegerEvaluation (E := E) (I := I) (G := G) n u hu z
        ⟨nativeLieExponential (I := nativeFiniteProductCorners I n) (G := nativeFiniteProduct G n)
          (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u x),
          (alignmentNativeFiniteImageSubgroup_mem_iff (E := E) (I := I) (G := G) n u _).mpr
            ⟨x, rfl⟩⟩ =
      nativeLieExponential (I := I) (G := G)
        (alignmentLiePolynomialArraysEvaluation (fun j => (z j : ℝ)) x) := by
  letI := nativeFiniteProductSimplyConnected (I := I) (G := G) n
  let f := alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u
  let e := f.equivRangeOfInjective hu
  let a := alignmentLiePolynomialArraysEvaluation (L := GroupLieAlgebra I G) (fun j => (z j : ℝ))
  let φ := a.comp e.symm.toLieHom
  have h := nativeLieSubalgebraIntegrate_exponential (E := nativeFiniteProduct E n) (F := E)
    (I := nativeFiniteProductCorners I n) (J := I) (G := nativeFiniteProduct G n) (K := G)
    f.range φ (e x)
  have hφ : φ (e x) = a x := congrArg a (e.symm_apply_apply x)
  exact h.trans (congrArg (nativeLieExponential (I := I) (G := G)) hφ)

theorem alignmentNativeIntegerEvaluation_continuous (n : ℕ) (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (z : σ → ℤ) :
    Continuous (alignmentNativeIntegerEvaluation (E := E) (I := I) (G := G) n u hu z) := by
  letI := nativeFiniteProductSimplyConnected (I := I) (G := G) n
  exact nativeLieSubalgebraIntegrate_continuous (E := nativeFiniteProduct E n) (F := E)
    (I := nativeFiniteProductCorners I n) (J := I) (G := nativeFiniteProduct G n) (K := G)
    (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u).range _

theorem alignmentNativeIntegerEvaluation_selected (n : ℕ) (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (g : alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u) (i : Fin (n + 1)) :
    alignmentNativeIntegerEvaluation (E := E) (I := I) (G := G) n u hu (u i) g =
      nativeFiniteProductCoordinate n g.val i := by
  obtain ⟨x, hx⟩ := (alignmentNativeFiniteImageSubgroup_mem_iff (E := E)
    (I := I) (G := G) n u g.val).mp g.property
  let p : alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u :=
    ⟨nativeLieExponential (I := nativeFiniteProductCorners I n) (G := nativeFiniteProduct G n)
      (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u x),
      (alignmentNativeFiniteImageSubgroup_mem_iff (E := E) (I := I) (G := G) n u _).mpr ⟨x, rfl⟩⟩
  have hp : p = g := Subtype.ext hx
  exact (congrArg (alignmentNativeIntegerEvaluation (E := E) (I := I) (G := G) n u hu (u i)) hp).symm.trans
    ((alignmentNativeIntegerEvaluation_exponential n u hu (u i) x).trans
      ((alignmentNativeFiniteImageSubgroup_coordinate n u x i).symm.trans
        (congrArg (fun v : nativeFiniteProduct G n => nativeFiniteProductCoordinate n v i) hx)))

end Hindman168
