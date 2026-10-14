import Hindman168.AlignmentPolynomialArrayLattice

namespace Hindman168
open scoped BigOperators Classical

def alignmentConstantArray {σ G : Type*} [Group G] (x : G) :
    alignmentPolynomialArrayGroup σ G :=
  ⟨fun _ => x, alignmentPolynomialArrayGroup_constant x⟩

noncomputable def alignmentPolynomialModelArray {σ G : Type*} [Fintype σ] [Group G]
    (g x : G) (k : ℤ) (Δ : σ → ℤ) : alignmentPolynomialArrayGroup σ G :=
  ⟨fun u => g ^ (k + ∑ j, u j * Δ j) * x,
    alignmentPolynomialArrayGroup_model g x k Δ⟩

noncomputable def alignmentPolynomialModelOrbit {σ G : Type*} [Fintype σ] [Group G]
    (g x : G) (k t : ℤ) (Δ : σ → ℤ) (ℓ : ℤ) : alignmentPolynomialArrayGroup σ G :=
  alignmentPolynomialModelArray g x (k + t * ℓ) Δ

theorem alignmentPolynomialModelArray_evaluation {σ G : Type*} [Fintype σ] [Group G]
    (g x : G) (k : ℤ) (Δ u : σ → ℤ) :
    alignmentPolynomialArrayEvaluation u (alignmentPolynomialModelArray g x k Δ) =
      g ^ (k + ∑ j, u j * Δ j) * x := rfl

theorem alignmentPolynomialModelArray_input_translation {σ G : Type*} [Fintype σ] [Group G]
    (g x : G) (k : ℤ) (Δ v : σ → ℤ) :
    alignmentPolynomialArrayTranslation v (alignmentPolynomialModelArray g x k Δ) =
      alignmentPolynomialModelArray g x (k + ∑ j, v j * Δ j) Δ := by
  apply Subtype.ext
  funext u
  change g ^ (k + ∑ j, (u + v) j * Δ j) * x =
    g ^ ((k + ∑ j, v j * Δ j) + ∑ j, u j * Δ j) * x
  have he : k + ∑ j, (u + v) j * Δ j =
      (k + ∑ j, v j * Δ j) + ∑ j, u j * Δ j := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  rw [he]

theorem alignmentConstantArray_power_evaluation {σ G : Type*} [Group G]
    (g : G) (t ℓ : ℤ) (u : σ → ℤ) :
    alignmentPolynomialArrayEvaluation u ((alignmentConstantArray (σ := σ) (g ^ t)) ^ ℓ) =
      g ^ (t * ℓ) := by
  rw [map_zpow]
  exact (zpow_mul g t ℓ).symm

theorem alignmentPolynomialModelOrbit_linear {σ G : Type*} [Fintype σ] [Group G]
    (g x : G) (k t : ℤ) (Δ : σ → ℤ) (ℓ : ℤ) :
    alignmentPolynomialModelOrbit g x k t Δ ℓ =
      alignmentConstantArray (g ^ t) ^ ℓ * alignmentPolynomialModelArray g x k Δ := by
  apply Subtype.ext
  funext u
  change alignmentPolynomialArrayEvaluation u (alignmentPolynomialModelOrbit g x k t Δ ℓ) =
    alignmentPolynomialArrayEvaluation u
      (alignmentConstantArray (g ^ t) ^ ℓ * alignmentPolynomialModelArray g x k Δ)
  rw [map_mul, alignmentConstantArray_power_evaluation,
    alignmentPolynomialModelArray_evaluation]
  change g ^ ((k + t * ℓ) + ∑ j, u j * Δ j) * x =
    g ^ (t * ℓ) * (g ^ (k + ∑ j, u j * Δ j) * x)
  rw [← mul_assoc, ← zpow_add]
  congr 2
  ring

end Hindman168
