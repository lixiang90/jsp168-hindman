import Hindman168.AlignmentNativeArrayTranslations
import Hindman168.AlignmentNativeLatticeMonomials

namespace Hindman168
open scoped Manifold ContDiff BigOperators TensorProduct

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

theorem alignmentNativeArrayGroup_polynomial_power (g : G)
    (p : MvPolynomial σ ℝ) (hp : p.totalDegree ≤ 1) (m : (σ → ℤ) → ℤ)
    (hm : ∀ z, MvPolynomial.aeval (fun j => (z j : ℝ)) p = (m z : ℝ)) :
    (fun z => g ^ m z) ∈ alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu := by
  let v : GroupLieAlgebra I G := nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g
  have hv : v ∈ LieModule.lowerCentralSeries ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G)
      (p.totalDegree - 1) := by
    rw [Nat.sub_eq_zero_of_le hp, LieModule.lowerCentralSeries_zero]
    exact LieSubmodule.mem_top v
  let c : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G) :=
    ⟨p ⊗ₜ[ℝ] v, alignmentLiePolynomialArrays_polynomial_tmul p v hv⟩
  apply (alignmentNativeAllIntegerArrayGroup_mem_iff n u hu _).mpr
  refine ⟨c, fun z => ?_⟩
  change nativeLieExponential (I := I) (G := G)
    (alignmentLieArrayEvaluation (fun j => (z j : ℝ)) (p ⊗ₜ[ℝ] v)) = _
  rw [alignmentLieArrayEvaluation_tmul, hm z]
  exact (nativeLieExponential_int_smul (E := E) (I := I) (G := G) v (m z)).trans
    (congrArg (fun a : G => a ^ m z) (nativeLieExponential_globalLogarithm (I := I) (G := G) g))

theorem alignmentNativeArrayGroup_constant (g : G) :
    (fun _ : σ → ℤ => g) ∈ alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu := by
  have h := alignmentNativeArrayGroup_polynomial_power n u hu g (MvPolynomial.C 1)
    (by simp) (fun _ => 1) (by intro z; simp)
  simpa only [zpow_one] using h

theorem alignmentNativeArrayGroup_affine_power [Fintype σ] (g : G) (k : ℤ) (Δ : σ → ℤ) :
    (fun z => g ^ (k + ∑ j, z j * Δ j)) ∈
      alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu := by
  classical
  let p : MvPolynomial σ ℝ := MvPolynomial.C (k : ℝ) +
    ∑ j, MvPolynomial.C (Δ j : ℝ) * MvPolynomial.X j
  have hp : p.totalDegree ≤ 1 := by
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le _
    · apply MvPolynomial.totalDegree_finsetSum_le
      intro j _
      exact (MvPolynomial.totalDegree_mul _ _).trans
        (by rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X])
  apply alignmentNativeArrayGroup_polynomial_power n u hu g p hp
  intro z
  simp only [p, map_add, map_sum, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, Int.cast_add, Int.cast_sum, Int.cast_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem alignmentNativeArrayGroup_model [Fintype σ] (g x : G) (k : ℤ) (Δ : σ → ℤ) :
    (fun z => g ^ (k + ∑ j, z j * Δ j) * x) ∈
      alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu :=
  (alignmentNativeAllIntegerArrayGroup n u hu).mul_mem
    (alignmentNativeArrayGroup_affine_power n u hu g k Δ)
    (alignmentNativeArrayGroup_constant n u hu x)

end Hindman168


