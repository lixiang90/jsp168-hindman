import Hindman168.AlignmentNativeArrayTranslations
import Hindman168.FiniteDeterminedArrayLattice

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

theorem alignmentNativeArrayTranslation_lattice (Γ : Subgroup G) (v : σ → ℤ) (f : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) :
    alignmentNativeArrayTranslation n u hu v f ∈ pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ ↔
      f ∈ pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ := by
  rw [pointwiseArrayLattice_mem, pointwiseArrayLattice_mem]
  constructor
  · intro h u
    have hu := h (u - v)
    change f.val ((u - v) + v) ∈ Γ at hu
    rw [sub_add_cancel] at hu
    exact hu
  · intro h u
    exact h (u + v)

noncomputable def alignmentNativeArrayCosetEvaluation (Γ : Subgroup G) (z : σ → ℤ) :
    alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸ pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ → G ⧸ Γ :=
  Quotient.lift (fun f : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu => (f.val z : G ⧸ Γ))
    (fun f h hfh => by
      apply QuotientGroup.eq.mpr
      have hmem := QuotientGroup.leftRel_apply.mp hfh
      exact (pointwiseArrayLattice_mem _ Γ (f⁻¹ * h)).mp hmem z)

theorem alignmentNativeArrayCosetEvaluation_mk (Γ : Subgroup G) (z : σ → ℤ) (f : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) :
    alignmentNativeArrayCosetEvaluation n u hu Γ z
      (f : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸ pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ) =
        (f.val z : G ⧸ Γ) := rfl

noncomputable def alignmentNativeArrayCosetTranslation (Γ : Subgroup G) (v : σ → ℤ) :
    alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸ pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ →
      alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸ pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ :=
  Quotient.lift (fun f : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu =>
      (alignmentNativeArrayTranslation n u hu v f :
        alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸ pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ))
    (fun f h hfh => by
      apply QuotientGroup.eq.mpr
      have hmem := QuotientGroup.leftRel_apply.mp hfh
      have hshift := (alignmentNativeArrayTranslation_lattice n u hu Γ v (f⁻¹ * h)).mpr hmem
      simpa only [map_mul, map_inv] using hshift)

theorem alignmentNativeArrayCosetTranslation_evaluation (Γ : Subgroup G) (v z : σ → ℤ)
    (y : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸ pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ) :
    alignmentNativeArrayCosetEvaluation n u hu Γ z (alignmentNativeArrayCosetTranslation n u hu Γ v y) =
      alignmentNativeArrayCosetEvaluation n u hu Γ (z + v) y := by
  induction y using Quotient.inductionOn with
  | _ f => rfl

theorem alignmentNativeArrayCosetEvaluation_continuous (Γ : Subgroup G) (z : σ → ℤ) :
    Continuous (alignmentNativeArrayCosetEvaluation n u hu Γ z) := by
  exact continuous_quot_lift _
    (QuotientGroup.continuous_mk.comp ((continuous_apply z).comp continuous_subtype_val))


theorem alignmentNativeArrayCosetTranslation_continuous (Γ : Subgroup G) (v : σ → ℤ) :
    Continuous (alignmentNativeArrayCosetTranslation n u hu Γ v) :=
  continuous_quot_lift _ (QuotientGroup.continuous_mk.comp
    (alignmentNativeArrayTranslation_continuous n u hu v))

theorem alignmentNativeArrayCosetTranslation_add (Γ : Subgroup G) (v w : σ → ℤ)
    (y : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸
      pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ) :
    alignmentNativeArrayCosetTranslation n u hu Γ v (alignmentNativeArrayCosetTranslation n u hu Γ w y) =
      alignmentNativeArrayCosetTranslation n u hu Γ (v + w) y := by
  induction y using Quotient.inductionOn with
  | _ a =>
    change (QuotientGroup.mk (alignmentNativeArrayTranslation n u hu v
      (alignmentNativeArrayTranslation n u hu w a))) = _
    rw [alignmentNativeArrayTranslation_add]
    rfl

theorem alignmentNativeArrayCosetTranslation_zero (Γ : Subgroup G)
    (y : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸
      pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ) :
    alignmentNativeArrayCosetTranslation n u hu Γ 0 y = y := by
  induction y using Quotient.inductionOn with
  | _ a =>
    have h : alignmentNativeArrayTranslation n u hu 0 a = a := by
      apply Subtype.ext
      funext z
      change a.val (z + 0) = a.val z
      rw [add_zero]
    exact congrArg QuotientGroup.mk h

noncomputable def alignmentNativeArrayCosetTranslationHomeomorph (Γ : Subgroup G) (v : σ → ℤ) :
    (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸
      pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ) ≃ₜ
    (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸
      pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ) where
  toFun := alignmentNativeArrayCosetTranslation n u hu Γ v
  invFun := alignmentNativeArrayCosetTranslation n u hu Γ (-v)
  left_inv y := by
    rw [alignmentNativeArrayCosetTranslation_add, neg_add_cancel,
      alignmentNativeArrayCosetTranslation_zero]
  right_inv y := by
    rw [alignmentNativeArrayCosetTranslation_add, add_neg_cancel,
      alignmentNativeArrayCosetTranslation_zero]
  continuous_toFun := alignmentNativeArrayCosetTranslation_continuous n u hu Γ v
  continuous_invFun := alignmentNativeArrayCosetTranslation_continuous n u hu Γ (-v)

end Hindman168
