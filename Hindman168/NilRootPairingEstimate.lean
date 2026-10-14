import Hindman168.NilPieceDualPairing

/-! The original pairing splits into its actual selected-dual pairing,
a small approximation cost and the unnormalized weighted boundary cost. -/

namespace Hindman168
open scoped BigOperators Classical
open FiniteMass

theorem finiteMass_goodRoot_pairing_bound {α : Type*}
    (μ : Mass α) (hμ : ∀ y, 0 ≤ μ y) (e weight f q : α → ℝ)
    (hweight : ∀ y ∈ μ.support, 0 ≤ weight y)
    (he : ∀ y ∈ μ.support, |e y| ≤ weight y)
    (good : α → Prop) (δ C : ℝ) (hδ : 0 ≤ δ)
    (hgood : ∀ y ∈ μ.support, good y → |f y - q y| ≤ δ)
    (hbad : ∀ y ∈ μ.support, ¬ good y → |f y - q y| ≤ C) :
    |expectation μ (fun y => e y * f y)| ≤
      |expectation μ (fun y => e y * q y)| + δ * expectation μ weight +
        C * expectation μ (fun y => if good y then 0 else weight y) := by
  have hb := finiteMass_goodRoot_weighted_error μ hμ e weight f q hweight he good δ C hδ hgood hbad
  have hid : expectation μ (fun y => e y * f y) =
      expectation μ (fun y => e y * (f y - q y)) + expectation μ (fun y => e y * q y) := by
    rw [← expectation_add]
    congr 1
    funext y
    ring
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith)

theorem pieceRecipeOriginalDual_badRoot_error {X P : Type*} [TopologicalSpace X]
    {d L n N K : ℕ} (recipes : Fin L → CornerProductRecipe (CubeVertex d) X)
    (hb : ∀ r, CornerProductRecipe.Bounded (recipes r))
    (piece : ℤ → P) (chooseRecipe : P → Fin L) (point : P → ℤ → X)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (choice : ℕ → Fin K)
    (J : Fin K → ℕ) (w : ℕ) (he : 0 < F.exponent w)
    (hT : 0 < F.gap w (gap w).val / (J (choice w) * (F.modulus w : ℕ)))
    (S : ℤ → ℝ) (B : ℝ) (hS : ∀ y, |S y| ≤ B) (y : ℤ) :
    |S y - pieceRecipeZeroDualSum (n := n) recipes piece chooseRecipe point F gap choice J w y| ≤
      (∑ r, (recipes r).coefficientMass) + B := by
  have ht := abs_sub_le (S y) 0
    (pieceRecipeZeroDualSum (n := n) recipes piece chooseRecipe point F gap choice J w y)
  simp only [sub_zero, zero_sub, abs_neg] at ht
  have hq := pieceRecipeOriginalDual_abs_le (n := n) recipes hb piece chooseRecipe point F gap choice J w y he hT
  linarith [hS y]

theorem pieceRecipeOriginalDual_weighted_pairing_bound {X P : Type*} [TopologicalSpace X]
    {d L n N K : ℕ} (recipes : Fin L → CornerProductRecipe (CubeVertex d) X)
    (hb : ∀ r, CornerProductRecipe.Bounded (recipes r))
    (piece : ℤ → P) (chooseRecipe : P → Fin L) (point : P → ℤ → X)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (choice : ℕ → Fin K)
    (J : Fin K → ℕ) (w : ℕ) (hexp : 0 < F.exponent w)
    (hT : 0 < F.gap w (gap w).val / (J (choice w) * (F.modulus w : ℕ)))
    (μ : Mass ℤ) (hμ : ∀ y, 0 ≤ μ y) (e weight S : ℤ → ℝ)
    (hweight : ∀ y ∈ μ.support, 0 ≤ weight y) (he : ∀ y ∈ μ.support, |e y| ≤ weight y)
    (B : ℝ) (hS : ∀ y, |S y| ≤ B) (good : ℤ → Prop) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ y ∈ μ.support, good y →
      |S y - pieceRecipeZeroDualSum (n := n) recipes piece chooseRecipe point F gap choice J w y| ≤ δ) :
    |expectation μ (fun y => e y * S y)| ≤
      |expectation μ (fun y => e y * pieceRecipeZeroDualSum (n := n)
        recipes piece chooseRecipe point F gap choice J w y)| +
      δ * expectation μ weight + ((∑ r, (recipes r).coefficientMass) + B) *
        expectation μ (fun y => if good y then 0 else weight y) := by
  apply finiteMass_goodRoot_pairing_bound μ hμ e weight S _ hweight he good δ _ hδ ha
  intro y _ _
  exact pieceRecipeOriginalDual_badRoot_error (n := n) recipes hb piece chooseRecipe point F gap choice J w hexp hT S B hS y

end Hindman168
