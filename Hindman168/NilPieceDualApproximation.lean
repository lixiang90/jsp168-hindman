import Hindman168.NilPieceLinearOrbits
import Hindman168.FiniteRestrictedDomination

/-! Actual zero-prime shift averages inherit root approximation on
interior roots. Weighted deletion retains the original mass and the
original majorant; it does not normalize boundary roots or divisor draws. -/

namespace Hindman168
open scoped BigOperators Classical
open FiniteMass

variable {d : ℕ}

theorem zeroPrimeRecipeShiftMass_nonneg (R J M : ℕ) (z : Fin d × Bool → ℤ) :
    0 ≤ zeroPrimeRecipeShiftMass d R J M z :=
  piMass_nonneg _ (fun _ => uniformIntervalMass_nonneg _ _) z

theorem zeroPrimeRecipeShiftMass_total (R J M : ℕ) (hT : 0 < R / (J * M)) :
    total (zeroPrimeRecipeShiftMass d R J M) = 1 :=
  piMass_total_one _ (fun _ => uniformIntervalMass_total 0 hT)

variable {X P : Type*} [TopologicalSpace X] {L n N K : ℕ}

theorem pieceRecipeOriginalDual_abs_le
    (recipes : Fin L → CornerProductRecipe (CubeVertex d) X)
    (hb : ∀ r, CornerProductRecipe.Bounded (recipes r))
    (piece : ℤ → P) (chooseRecipe : P → Fin L) (point : P → ℤ → X)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (choice : ℕ → Fin K)
    (J : Fin K → ℕ) (w : ℕ) (y : ℤ) (he : 0 < F.exponent w)
    (hT : 0 < F.gap w (gap w).val / (J (choice w) * (F.modulus w : ℕ))) :
    |pieceRecipeZeroDualSum (n := n) recipes piece chooseRecipe point F gap choice J w y| ≤
      ∑ r, (recipes r).coefficientMass := by
  rw [pieceRecipeZeroDualSum_eq_expectation recipes piece chooseRecipe point F gap choice J w y he]
  have h := expectation_difference_support_bound
    (zeroPrimeRecipeShiftMass d (F.gap w (gap w).val) (J (choice w)) (F.modulus w : ℕ))
    (zeroPrimeRecipeShiftMass_nonneg _ _ _)
    (fun z => pieceRecipeCubeSum recipes piece chooseRecipe point (zeroPrimeRecipeVertex (F.modulus w : ℕ) y z))
    (fun _ => 0) (∑ r, (recipes r).coefficientMass)
    (fun z _ => by simpa only [sub_zero] using pieceRecipeCubeSum_abs_le recipes hb piece chooseRecipe point _)
  simpa only [expectation_const, mul_zero, sub_zero, zeroPrimeRecipeShiftMass_total _ _ _ hT, one_mul] using h

omit [TopologicalSpace X] in
theorem finiteMass_goodRoot_weighted_error {α : Type*}
    (μ : Mass α) (hμ : ∀ y, 0 ≤ μ y) (e weight f q : α → ℝ)
    (hweight : ∀ y ∈ μ.support, 0 ≤ weight y)
    (he : ∀ y ∈ μ.support, |e y| ≤ weight y)
    (good : α → Prop) (δ C : ℝ) (hδ : 0 ≤ δ)
    (hgood : ∀ y ∈ μ.support, good y → |f y - q y| ≤ δ)
    (hbad : ∀ y ∈ μ.support, ¬ good y → |f y - q y| ≤ C) :
    |expectation μ (fun y => e y * (f y - q y))| ≤
      δ * expectation μ weight + C * expectation μ (fun y => if good y then 0 else weight y) := by
  have hpoint (y : α) (hy : y ∈ μ.support) :
      |e y * (f y - q y)| ≤ δ * weight y + C * (if good y then 0 else weight y) := by
    rw [abs_mul]
    by_cases hg : good y
    · simp only [if_pos hg, mul_zero, add_zero]
      calc
        _ ≤ weight y * δ := mul_le_mul (he y hy) (hgood y hy hg) (abs_nonneg _) (hweight y hy)
        _ = δ * weight y := mul_comm _ _
    · simp only [if_neg hg]
      calc
        _ ≤ weight y * C := mul_le_mul (he y hy) (hbad y hy hg) (abs_nonneg _) (hweight y hy)
        _ = C * weight y := mul_comm _ _
        _ ≤ δ * weight y + C * weight y := le_add_of_nonneg_left (mul_nonneg hδ (hweight y hy))
  have h := abs_expectation_le_majorant_support μ _ _ hμ hpoint
  simpa only [expectation_add, expectation_const_mul] using h

omit [TopologicalSpace X] in
theorem pieceRecipeOriginalDual_linear_good_root {G : Type*} [Group G]
    (Γ : Subgroup G) [TopologicalSpace (G ⧸ Γ)]
    (recipes : Fin L → CornerProductRecipe (CubeVertex d) (G ⧸ Γ))
    (chooseRecipe : (ℤ × ℤ) → Fin L) (obs : (ℤ × ℤ) → C(G ⧸ Γ, ℝ))
    (g x : (ℤ × ℤ) → G) (δ : ℝ)
    (ha : ∀ p, ∀ b₀ : ℤ, ∀ b : Fin d → ℤ,
      |(recipes (chooseRecipe p)).value
        (fun E => (g p ^ (b₀ + ∑ j ∈ E.val, b j) * x p : G ⧸ Γ)) - obs p (g p ^ b₀ * x p)| ≤ δ)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (choice : ℕ → Fin K)
    (J : Fin K → ℕ) (w : ℕ) (y : ℤ) (he : 0 < F.exponent w)
    (hd : 0 < d) (hR : 0 < F.gap w (gap w).val)
    (hT : 0 < F.gap w (gap w).val / (J (choice w) * (F.modulus w : ℕ)))
    (hy : intervalInteriorRoot (F.gap w (gap w).val)
      (zeroPrimeCubeMargin d (F.gap w (gap w).val) (J (choice w)) (F.modulus w : ℕ)) y) :
    |pieceRecipeZeroDualSum (n := n) recipes
      (intervalResiduePiece (F.gap w (gap w).val) (F.modulus w : ℕ)) chooseRecipe
      (pieceLinearOrbit Γ (F.modulus w : ℕ) g x) F gap choice J w y -
      obs (intervalResiduePiece (F.gap w (gap w).val) (F.modulus w : ℕ) y)
        (pieceLinearOrbit Γ (F.modulus w : ℕ) g x
          (intervalResiduePiece (F.gap w (gap w).val) (F.modulus w : ℕ) y) y)| ≤ δ := by
  rw [pieceRecipeZeroDualSum_eq_expectation recipes _ chooseRecipe _ F gap choice J w y he]
  have hM : 0 < (F.modulus w : ℕ) := (F.modulus w).pos
  have h := expectation_difference_support_bound
    (zeroPrimeRecipeShiftMass d (F.gap w (gap w).val) (J (choice w)) (F.modulus w : ℕ))
    (zeroPrimeRecipeShiftMass_nonneg _ _ _)
    (fun z => pieceRecipeCubeSum recipes
      (intervalResiduePiece (F.gap w (gap w).val) (F.modulus w : ℕ)) chooseRecipe
      (pieceLinearOrbit Γ (F.modulus w : ℕ) g x) (zeroPrimeRecipeVertex (F.modulus w : ℕ) y z))
    (fun _ => obs (intervalResiduePiece (F.gap w (gap w).val) (F.modulus w : ℕ) y)
      (pieceLinearOrbit Γ (F.modulus w : ℕ) g x
        (intervalResiduePiece (F.gap w (gap w).val) (F.modulus w : ℕ) y) y)) δ
    (fun z hz => pieceRecipeCubeSum_linear_good_root Γ recipes chooseRecipe obs g x
      _ _ _ hR hM hd δ ha y hy z hz)
  simpa only [expectation_const, zeroPrimeRecipeShiftMass_total _ _ _ hT, one_mul] using h

theorem pieceRecipeOriginalDual_error_bound
    (recipes : Fin L → CornerProductRecipe (CubeVertex d) X)
    (hb : ∀ r, CornerProductRecipe.Bounded (recipes r))
    (piece : ℤ → P) (chooseRecipe : P → Fin L) (point : P → ℤ → X)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (choice : ℕ → Fin K)
    (J : Fin K → ℕ) (w : ℕ) (he : 0 < F.exponent w)
    (hT : 0 < F.gap w (gap w).val / (J (choice w) * (F.modulus w : ℕ)))
    (S : ℤ → ℝ) (B : ℝ) (hS : ∀ y, |S y| ≤ B) (δ : ℝ) (hδ : 0 ≤ δ)
    (good : ℤ → Prop)
    (ha : ∀ y, good y →
      |S y - pieceRecipeZeroDualSum (n := n) recipes piece chooseRecipe point F gap choice J w y| ≤ δ)
    (y : ℤ) :
    |S y - pieceRecipeZeroDualSum (n := n) recipes piece chooseRecipe point F gap choice J w y| ≤
      δ + (if good y then 0 else (∑ r, (recipes r).coefficientMass) + B) := by
  by_cases hg : good y
  · simpa only [if_pos hg, add_zero] using ha y hg
  · rw [if_neg hg]
    have htri := abs_sub_le (S y) 0
      (pieceRecipeZeroDualSum (n := n) recipes piece chooseRecipe point F gap choice J w y)
    simp only [sub_zero, zero_sub, abs_neg] at htri
    have h := htri.trans (add_le_add (hS y)
      (pieceRecipeOriginalDual_abs_le recipes hb piece chooseRecipe point F gap choice J w y he hT))
    linarith

end Hindman168
