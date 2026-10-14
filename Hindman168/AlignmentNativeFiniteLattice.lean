import Hindman168.AlignmentNativeArrayLattice
import Hindman168.AlignmentNativeLatticeMonomials

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

/-! The original pointwise lattice pulled back to the actual finite image,
and then included in the ambient finite product. No finite-input-only
lattice replaces the requirement at every integer input. -/

noncomputable def alignmentNativeFiniteLattice (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (Γ : Subgroup G) : Subgroup (alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u) :=
  (pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ).comap
    (alignmentNativeArrayEquiv n u hu).toMonoidHom

theorem alignmentNativeFiniteLattice_mem (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (Γ : Subgroup G) (g : alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u) :
    g ∈ alignmentNativeFiniteLattice n u hu Γ ↔
      ∀ z : σ → ℤ, alignmentNativeIntegerEvaluation (E := E) (I := I) (G := G) n u hu z g ∈ Γ := by
  change (alignmentNativeArrayEquiv n u hu) g ∈ pointwiseArrayLattice _ Γ ↔ _
  rw [pointwiseArrayLattice_mem]
  rfl

theorem alignmentNativeFiniteLattice_discrete (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (Γ : Subgroup G) [DiscreteTopology Γ] :
    DiscreteTopology (alignmentNativeFiniteLattice n u hu Γ) := by
  letI := alignmentNativeArrayLattice_discrete (E := E) (I := I) n u hu Γ
  let f : alignmentNativeFiniteLattice n u hu Γ →
      pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ :=
    fun g => ⟨alignmentNativeArrayEquiv n u hu g.val, g.property⟩
  apply discreteTopology_of_continuous_injective f
  · exact ((alignmentNativeArrayHomeomorph n u hu).continuous.comp continuous_subtype_val).subtype_mk _
  · intro a b hab
    exact Subtype.ext ((alignmentNativeArrayEquiv n u hu).injective (congrArg Subtype.val hab))

noncomputable def alignmentNativeFiniteAmbientLattice (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (Γ : Subgroup G) : Subgroup (nativeFiniteProduct G n) :=
  (alignmentNativeFiniteLattice n u hu Γ).map
    (alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u).subtype

theorem alignmentNativeFiniteAmbientLattice_le (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (Γ : Subgroup G) :
    alignmentNativeFiniteAmbientLattice n u hu Γ ≤
      alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u := by
  rintro g ⟨a, _, rfl⟩
  exact a.property

theorem alignmentNativeFiniteAmbientLattice_exponential_mem_iff (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (Γ : Subgroup G) (x : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G)) :
    nativeLieExponential (I := nativeFiniteProductCorners I n) (G := nativeFiniteProduct G n)
      (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u x) ∈
        alignmentNativeFiniteAmbientLattice n u hu Γ ↔
      ∀ z : σ → ℤ, nativeLieExponential (I := I) (G := G)
        (alignmentLiePolynomialArraysEvaluation (fun j => (z j : ℝ)) x) ∈ Γ := by
  let a : alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u :=
    ⟨nativeLieExponential (I := nativeFiniteProductCorners I n) (G := nativeFiniteProduct G n)
      (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u x),
      (alignmentNativeFiniteImageSubgroup_mem_iff n u _).mpr ⟨x, rfl⟩⟩
  have he : a.val ∈ alignmentNativeFiniteAmbientLattice n u hu Γ ↔
      a ∈ alignmentNativeFiniteLattice n u hu Γ := by
    constructor
    · rintro ⟨b, hb, hba⟩
      exact (Subtype.ext hba : b = a) ▸ hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  change a.val ∈ _ ↔ _
  rw [he, alignmentNativeFiniteLattice_mem]
  exact forall_congr' fun z => by
    rw [alignmentNativeIntegerEvaluation_exponential]

end Hindman168

