import Hindman168.AlignmentNativeJointArrayGroup
import Hindman168.AlignmentNativeModelCosetOrbit

namespace Hindman168
open scoped Manifold ContDiff BigOperators

attribute [local instance 10] nativeFiniteProductTopologicalSpace
attribute [local instance] nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three

variable {ι : Type*} {σ E H G : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, CompleteSpace (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, TopologicalSpace (H i)]
  {I : ∀ i, ModelWithCorners ℝ (E i) (H i)}
  [∀ i, TopologicalSpace (G i)] [∀ i, ChartedSpace (H i) (G i)] [∀ i, Group (G i)]
  [∀ i, LieGroup (I i) ∞ (G i)] [∀ i, BoundarylessManifold (I i) (G i)]
  [∀ i, T2Space (G i)] [∀ i, Group.IsNilpotent (G i)]
  [∀ i, ConnectedSpace (G i)] [∀ i, SimplyConnectedSpace (G i)]
  (n : ι → ℕ) (u : ∀ i, Fin (n i + 1) → σ i → ℤ)
  (hu : ∀ i, Function.Injective (alignmentNativeFiniteEvaluation (E := E i) (I := I i) (G := G i) (n i) (u i)))

noncomputable def alignmentNativeJointModelArray [∀ i, Fintype (σ i)]
    (g x : ∀ i, G i) (k : ι → ℤ) (Δ : ∀ i, σ i → ℤ) : alignmentNativeJointArrayGroup n u hu :=
  fun i => alignmentNativeModelArray (n i) (u i) (hu i) (g i) (x i) (k i) (Δ i)

noncomputable def alignmentNativeJointModelOrbit [∀ i, Fintype (σ i)]
    (g x : ∀ i, G i) (k t : ι → ℤ) (Δ : ∀ i, σ i → ℤ) (ℓ : ℤ) :
    alignmentNativeJointArrayGroup n u hu :=
  fun i => alignmentNativeModelOrbit (n i) (u i) (hu i) (g i) (x i) (k i) (t i) (Δ i) ℓ

noncomputable def alignmentNativeJointModelStep (g : ∀ i, G i) (t : ι → ℤ) :
    alignmentNativeJointArrayGroup n u hu :=
  fun i => alignmentNativeConstantArray (n i) (u i) (hu i) (g i ^ t i)

theorem alignmentNativeJointModelOrbit_linear [∀ i, Fintype (σ i)]
    (g x : ∀ i, G i) (k t : ι → ℤ) (Δ : ∀ i, σ i → ℤ) (ℓ : ℤ) :
    alignmentNativeJointModelOrbit n u hu g x k t Δ ℓ =
      alignmentNativeJointModelStep n u hu g t ^ ℓ * alignmentNativeJointModelArray n u hu g x k Δ := by
  funext i
  exact alignmentNativeModelOrbit_linear (n i) (u i) (hu i) (g i) (x i) (k i) (t i) (Δ i) ℓ

noncomputable def alignmentNativeJointCosetEvaluation (Γ : ∀ i, Subgroup (G i)) (i : ι) (z : σ i → ℤ) :
    alignmentNativeJointArrayGroup n u hu ⧸ alignmentNativeJointArrayLattice n u hu Γ → G i ⧸ Γ i :=
  fun y => alignmentNativeArrayCosetEvaluation (n i) (u i) (hu i) (Γ i) z
    (piCosetMap (fun j => pointwiseArrayLattice _ (Γ j)) y i)

theorem alignmentNativeJointCosetEvaluation_continuous (Γ : ∀ i, Subgroup (G i)) (i : ι) (z : σ i → ℤ) :
    Continuous (alignmentNativeJointCosetEvaluation n u hu Γ i z) :=
  (alignmentNativeArrayCosetEvaluation_continuous (n i) (u i) (hu i) (Γ i) z).comp
    ((continuous_apply i).comp (piCosetMap_continuous _))

noncomputable def alignmentNativeJointModelCosetOrbit [∀ i, Fintype (σ i)]
    (Γ : ∀ i, Subgroup (G i)) (g x : ∀ i, G i) (k t : ι → ℤ) (Δ : ∀ i, σ i → ℤ) (ℓ : ℤ) :
    alignmentNativeJointArrayGroup n u hu ⧸ alignmentNativeJointArrayLattice n u hu Γ :=
  QuotientGroup.mk (alignmentNativeJointModelOrbit n u hu g x k t Δ ℓ)

theorem alignmentNativeJointModelCosetOrbit_evaluation [∀ i, Fintype (σ i)]
    (Γ : ∀ i, Subgroup (G i)) (g x : ∀ i, G i) (k t : ι → ℤ) (Δ : ∀ i, σ i → ℤ)
    (ℓ : ℤ) (i : ι) (z : σ i → ℤ) :
    alignmentNativeJointCosetEvaluation n u hu Γ i z (alignmentNativeJointModelCosetOrbit n u hu Γ g x k t Δ ℓ) =
      (g i ^ (k i + t i * ℓ + ∑ j, z j * Δ i j) * x i : G i ⧸ Γ i) := rfl

theorem alignmentNativeJointModelCosetOrbit_linear [∀ i, Fintype (σ i)]
    (Γ : ∀ i, Subgroup (G i)) (g x : ∀ i, G i) (k t : ι → ℤ) (Δ : ∀ i, σ i → ℤ) (ℓ : ℤ) :
    alignmentNativeJointModelCosetOrbit n u hu Γ g x k t Δ ℓ =
      (alignmentNativeJointModelStep n u hu g t ^ ℓ) •
        (QuotientGroup.mk (alignmentNativeJointModelArray n u hu g x k Δ) :
          alignmentNativeJointArrayGroup n u hu ⧸ alignmentNativeJointArrayLattice n u hu Γ) := by
  unfold alignmentNativeJointModelCosetOrbit
  rw [alignmentNativeJointModelOrbit_linear]
  rfl

end Hindman168
