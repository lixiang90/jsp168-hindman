import Hindman168.AlignmentNativeJointTranslations
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

noncomputable def alignmentNativeJointReading (Γ : ∀ i, Subgroup (G i))
    (i : ι) (f : C(G i ⧸ Γ i, ℝ)) (z : σ i → ℤ) :
    C(alignmentNativeJointArrayGroup n u hu ⧸ alignmentNativeJointArrayLattice n u hu Γ, ℝ) :=
  f.comp ⟨alignmentNativeJointCosetEvaluation n u hu Γ i z,
    alignmentNativeJointCosetEvaluation_continuous n u hu Γ i z⟩

theorem alignmentNativeJointReading_modelOrbit [∀ i, Fintype (σ i)]
    (Γ : ∀ i, Subgroup (G i)) (i : ι) (f : C(G i ⧸ Γ i, ℝ))
    (g x : ∀ i, G i) (k t : ι → ℤ) (Δ : ∀ i, σ i → ℤ) (z : σ i → ℤ) (ℓ : ℤ) :
    alignmentNativeJointReading n u hu Γ i f z
      (alignmentNativeJointModelCosetOrbit n u hu Γ g x k t Δ ℓ) =
      f ((g i ^ (k i + t i * ℓ + ∑ j, z j * Δ i j) * x i : G i ⧸ Γ i)) := rfl

theorem alignmentNativeJointReading_bound (Γ : ∀ i, Subgroup (G i))
    (i : ι) (f : C(G i ⧸ Γ i, ℝ)) (B : ℝ) (hf : ∀ x, |f x| ≤ B) (z : σ i → ℤ)
    (y : alignmentNativeJointArrayGroup n u hu ⧸ alignmentNativeJointArrayLattice n u hu Γ) :
    |alignmentNativeJointReading n u hu Γ i f z y| ≤ B := hf _

theorem alignmentNativeJointReading_difference_bound (Γ : ∀ i, Subgroup (G i))
    (i : ι) (f f' : C(G i ⧸ Γ i, ℝ)) (ε : ℝ)
    (hf : ∀ x, |f x - f' x| ≤ ε) (z : σ i → ℤ)
    (y : alignmentNativeJointArrayGroup n u hu ⧸ alignmentNativeJointArrayLattice n u hu Γ) :
    |alignmentNativeJointReading n u hu Γ i f z y -
      alignmentNativeJointReading n u hu Γ i f' z y| ≤ ε := hf _

theorem alignmentNativeJointReading_translation (Γ : ∀ i, Subgroup (G i))
    (i : ι) (f : C(G i ⧸ Γ i, ℝ)) (v : ∀ i, σ i → ℤ) (z : σ i → ℤ)
    (y : alignmentNativeJointArrayGroup n u hu ⧸ alignmentNativeJointArrayLattice n u hu Γ) :
    alignmentNativeJointReading n u hu Γ i f z
      (alignmentNativeJointCosetTranslation n u hu Γ v y) =
      alignmentNativeJointReading n u hu Γ i f (z + v i) y := by
  change f (alignmentNativeJointCosetEvaluation n u hu Γ i z
    (alignmentNativeJointCosetTranslation n u hu Γ v y)) = _
  rw [alignmentNativeJointCosetTranslation_evaluation]
  rfl

end Hindman168
