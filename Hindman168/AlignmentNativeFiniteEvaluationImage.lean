import Hindman168.NativeFiniteProductExponential
import Hindman168.AlignmentNativeLieArrayFiniteEvaluations

/-! The complete array coefficient algebra embeds by actual integer
evaluations into the native Lie algebra of an actual finite product of
the original group. The evaluation set is chosen before the coefficients. -/

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
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

noncomputable def alignmentNativeFiniteEvaluation (n : ℕ) (u : Fin (n + 1) → σ → ℤ) :
    alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G) →ₗ⁅ℝ⁆
      GroupLieAlgebra (nativeFiniteProductCorners I n) (nativeFiniteProduct G n) :=
  nativeFiniteProductLieMap n
    (fun i => alignmentLiePolynomialArraysEvaluation (fun j => (u i j : ℝ)))

theorem alignmentNativeFiniteEvaluation_coordinate (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (x : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G)) (i : Fin (n + 1)) :
    (show GroupLieAlgebra I G from
      nativeFiniteProductCoordinate n
        (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u x) i) =
      alignmentLiePolynomialArraysEvaluation (fun j => (u i j : ℝ)) x :=
  nativeFiniteProductLieMap_coordinate (E := E) (I := I) (G := G) n _ x i

variable [Finite σ] [FiniteDimensional ℝ E] [Group.IsNilpotent G]

theorem alignmentNativeFiniteEvaluation_exists_injective :
    ∃ (n : ℕ) (u : Fin (n + 1) → σ → ℤ),
      Function.Injective (alignmentNativeFiniteEvaluation (I := I) (G := G) n u) := by
  classical
  obtain ⟨S, hS⟩ := alignmentNativeLieArray_finite_integer_embedding (σ := σ) (I := I) (G := G)
  let T : Finset (σ → ℤ) := insert 0 S
  have hT : 0 < T.card := Finset.card_pos.mpr ⟨0, Finset.mem_insert_self _ _⟩
  let n := T.card - 1
  have hcard : Fintype.card T = n + 1 := by
    simpa only [Fintype.card_coe] using (show T.card = n + 1 by omega)
  let e : Fin (n + 1) ≃ T := (finCongr hcard.symm).trans (Fintype.equivFin T).symm
  let u : Fin (n + 1) → σ → ℤ := fun i => (e i).val
  refine ⟨n, u, nativeFiniteProductLieMap_injective n _ ?_⟩
  intro x y hxy
  apply hS
  funext z
  let t : T := ⟨z.val, Finset.mem_insert_of_mem z.property⟩
  have ht := congrFun hxy (e.symm t)
  change alignmentLiePolynomialArraysEvaluation (fun j => ((e (e.symm t)).val j : ℝ)) x =
    alignmentLiePolynomialArraysEvaluation (fun j => ((e (e.symm t)).val j : ℝ)) y at ht
  rw [e.apply_symm_apply] at ht
  exact ht

end Hindman168
