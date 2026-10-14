import Hindman168.AlignmentNativeFiniteEvaluationImage

/-! Integrate the complete finite evaluation image of the genuine array
coefficient algebra inside the actual original-group finite product.
No all-integer array multiplication or lattice compactness is assumed. -/

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

noncomputable def alignmentNativeFiniteImageSubgroup (n : ℕ) (u : Fin (n + 1) → σ → ℤ) :
    Subgroup (nativeFiniteProduct G n) :=
  nativeLieSubalgebraSubgroup (I := nativeFiniteProductCorners I n)
    (G := nativeFiniteProduct G n) (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u).range

theorem alignmentNativeFiniteImageSubgroup_mem_iff (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ) (g : nativeFiniteProduct G n) :
    g ∈ alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u ↔
      ∃ x : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G),
        nativeLieExponential (I := nativeFiniteProductCorners I n)
          (G := nativeFiniteProduct G n) (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u x) = g := by
  unfold alignmentNativeFiniteImageSubgroup
  rw [nativeLieSubalgebraSubgroup_mem_iff]
  constructor
  · rintro ⟨v, hv, hg⟩
    change (show GroupLieAlgebra (nativeFiniteProductCorners I n)
      (nativeFiniteProduct G n) from v) ∈ (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u).range at hv
    obtain ⟨x, hx⟩ := (LieHom.mem_range (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u) _).mp hv
    exact ⟨x, (congrArg (nativeLieExponential (I := nativeFiniteProductCorners I n)
      (G := nativeFiniteProduct G n)) hx).trans hg⟩
  · rintro ⟨x, hx⟩
    exact ⟨_, (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u).mem_range_self x, hx⟩

omit [FiniteDimensional ℝ E] [Group.IsNilpotent G] in
theorem alignmentNativeFiniteImageSubgroup_coordinate (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (x : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G)) (i : Fin (n + 1)) :
    nativeFiniteProductCoordinate n
        (nativeLieExponential (I := nativeFiniteProductCorners I n)
          (G := nativeFiniteProduct G n) (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u x)) i =
      nativeLieExponential (I := I) (G := G)
        (alignmentLiePolynomialArraysEvaluation (fun j => (u i j : ℝ)) x) :=
  nativeFiniteProductLieMap_exponential_coordinate n _ x i

variable [ConnectedSpace G] [SimplyConnectedSpace G]

theorem alignmentNativeFiniteImageExponential_injective (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u)) :
    Function.Injective (fun x => nativeLieExponential (I := nativeFiniteProductCorners I n)
      (G := nativeFiniteProduct G n) (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u x)) := by
  letI := nativeFiniteProductSimplyConnected (I := I) (G := G) n
  exact (nativeLieExponential_injective (I := nativeFiniteProductCorners I n)
    (G := nativeFiniteProduct G n)).comp hu

theorem alignmentNativeFiniteImageSubgroup_closed (n : ℕ) (u : Fin (n + 1) → σ → ℤ) :
    IsClosed (alignmentNativeFiniteImageSubgroup (I := I) (G := G) n u :
      Set (nativeFiniteProduct G n)) := by
  letI := nativeFiniteProductSimplyConnected (I := I) (G := G) n
  exact nativeLieSubalgebraSubgroup_closed (E := nativeFiniteProduct E n)
    (I := nativeFiniteProductCorners I n) (G := nativeFiniteProduct G n)
    (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u).range

theorem alignmentNativeFiniteImageSubgroup_contractible (n : ℕ) (u : Fin (n + 1) → σ → ℤ) :
    ContractibleSpace (alignmentNativeFiniteImageSubgroup (I := I) (G := G) n u) := by
  letI := nativeFiniteProductSimplyConnected (I := I) (G := G) n
  exact nativeLieSubalgebraSubgroup_contractible (E := nativeFiniteProduct E n)
    (I := nativeFiniteProductCorners I n) (G := nativeFiniteProduct G n)
    (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u).range

theorem alignmentNativeFiniteImageSubgroup_simplyConnected (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ) :
    SimplyConnectedSpace (alignmentNativeFiniteImageSubgroup (I := I) (G := G) n u) := by
  letI := alignmentNativeFiniteImageSubgroup_contractible (E := E) (I := I) (G := G) n u
  infer_instance

theorem alignmentNativeFiniteImage_exists [Finite σ] :
    ∃ (n : ℕ) (u : Fin (n + 1) → σ → ℤ),
      Function.Injective (fun x => nativeLieExponential (I := nativeFiniteProductCorners I n)
        (G := nativeFiniteProduct G n) (alignmentNativeFiniteEvaluation (E := E) (I := I) n u x)) ∧
      IsClosed (alignmentNativeFiniteImageSubgroup (I := I) (G := G) n u :
        Set (nativeFiniteProduct G n)) ∧
      SimplyConnectedSpace (alignmentNativeFiniteImageSubgroup (I := I) (G := G) n u) := by
  obtain ⟨n, u, hu⟩ := alignmentNativeFiniteEvaluation_exists_injective (σ := σ) (I := I) (G := G)
  exact ⟨n, u, alignmentNativeFiniteImageExponential_injective n u hu,
    alignmentNativeFiniteImageSubgroup_closed n u,
    alignmentNativeFiniteImageSubgroup_simplyConnected n u⟩

end Hindman168
