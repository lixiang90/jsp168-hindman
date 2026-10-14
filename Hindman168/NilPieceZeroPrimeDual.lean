import Hindman168.NilPieceRecipeSelectors
import Hindman168.OriginalZeroPrimeTemplate
import Hindman168.FiniteConvexPowerExpansion
import Hindman168.FiniteWeightedErrors

/-! Piece selectors are actual inputs to the original zero-prime template
with its original master modulus. A finite sum of those exact dual tests
is precisely the original shift average of the selected cube recipes. -/

namespace Hindman168
open scoped BigOperators Classical
open FiniteMass

variable {X P : Type*} [TopologicalSpace X] {d L : ℕ}

noncomputable def pieceRecipeDualInput (piece : ℤ → P) (chooseRecipe : P → Fin L)
    (point : P → ℤ → X) (r : Fin L) (factor : CubeVertex d → C(X, ℝ)) :
    OriginalSingleDualInput 0 d where
  epsilon := fun _ => 1
  vertexTest := fun _ => pieceRecipeFactor piece chooseRecipe point r factor

noncomputable def zeroPrimeRecipeShiftMass (d R J M : ℕ) : Mass (Fin d × Bool → ℤ) :=
  piMass (fun _ => uniformIntervalMass 0 (R / (J * M)))

def zeroPrimeRecipeVertex (M : ℕ) (y : ℤ) (z : Fin d × Bool → ℤ) : CubeVertex d → ℤ :=
  fun S => y + (M : ℤ) * ∑ j ∈ S.val, (z (j, true) - z (j, false))

noncomputable def pieceRecipeZeroDualSum {n N K : ℕ}
    (recipes : Fin L → CornerProductRecipe (CubeVertex d) X)
    (piece : ℤ → P) (chooseRecipe : P → Fin L) (point : P → ℤ → X)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (choice : ℕ → Fin K)
    (J : Fin K → ℕ) (w : ℕ) (y : ℤ) : ℝ :=
  ∑ r, ((recipes r).map (fun t => t.1 *
    (originalZeroPrimeTemplate (n := n) d gap choice).dual F J
      (pieceRecipeDualInput piece chooseRecipe point r t.2) w y)).sum

omit [TopologicalSpace X] in
theorem cubeVertex_nonempty_of_pos (hd : 0 < d) : Nonempty (CubeVertex d) := by
  exact ⟨⟨{⟨0, hd⟩}, by simp⟩⟩

theorem pieceRecipeDualInput_admissible {m : ℕ} (piece : ℤ → P)
    (chooseRecipe : P → Fin L) (point : P → ℤ → X) (r : Fin L)
    (factor : CubeVertex d → C(X, ℝ)) (hb : ∀ j x, |factor j x| ≤ 1)
    (F : MasterParameterFamily) (C : ℕ → Chain m) (label : ℕ → Fin m) (w : ℕ)
    (hν : ∀ y, 0 ≤ masterPredictionBlockMask F C label w y) :
    (pieceRecipeDualInput piece chooseRecipe point r factor).Admissible F C label w := by
  refine ⟨fun _ => by norm_num [pieceRecipeDualInput], ?_⟩
  intro _ S y
  exact (pieceRecipeFactor_abs_le piece chooseRecipe point r factor hb S y).trans (by linarith [hν y])

theorem pieceRecipeDualInput_zeroPrime_formula {n N K : ℕ}
    (piece : ℤ → P) (chooseRecipe : P → Fin L) (point : P → ℤ → X)
    (r : Fin L) (factor : CubeVertex d → C(X, ℝ))
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (choice : ℕ → Fin K)
    (J : Fin K → ℕ) (w : ℕ) (y : ℤ) (he : 0 < F.exponent w) :
    (originalZeroPrimeTemplate (n := n) d gap choice).dual F J
      (pieceRecipeDualInput piece chooseRecipe point r factor) w y =
    expectation (zeroPrimeRecipeShiftMass d (F.gap w (gap w).val)
      (J (choice w)) (F.modulus w : ℕ))
      (fun z => ∏ S, pieceRecipeFactor piece chooseRecipe point r factor S
        (zeroPrimeRecipeVertex (F.modulus w : ℕ) y z S)) := by
  rw [originalZeroPrimeTemplate_dual d gap choice F J _ w y he]
  simp only [pieceRecipeDualInput, zeroPrimeRecipeShiftMass, zeroPrimeRecipeVertex, one_mul]
  rfl

omit [TopologicalSpace X] in
theorem finiteMass_expectation_list_map_sum {α β : Type*}
    (μ : Mass α) (s : List β) (f : β → α → ℝ) :
    expectation μ (fun x => (s.map (fun t => f t x)).sum) =
      (s.map (fun t => expectation μ (f t))).sum := by
  induction s with
  | nil => simp [expectation]
  | cons t s ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [expectation_add, ih]

theorem pieceRecipeZeroDualSum_eq_expectation {n N K : ℕ}
    (recipes : Fin L → CornerProductRecipe (CubeVertex d) X)
    (piece : ℤ → P) (chooseRecipe : P → Fin L) (point : P → ℤ → X)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (choice : ℕ → Fin K)
    (J : Fin K → ℕ) (w : ℕ) (y : ℤ) (he : 0 < F.exponent w) :
    pieceRecipeZeroDualSum (n := n) recipes piece chooseRecipe point F gap choice J w y =
      expectation (zeroPrimeRecipeShiftMass d (F.gap w (gap w).val)
        (J (choice w)) (F.modulus w : ℕ))
        (fun z => pieceRecipeCubeSum recipes piece chooseRecipe point
          (zeroPrimeRecipeVertex (F.modulus w : ℕ) y z)) := by
  unfold pieceRecipeZeroDualSum pieceRecipeCubeSum
  symm
  rw [expectation_finset_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [finiteMass_expectation_list_map_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  rw [expectation_const_mul, pieceRecipeDualInput_zeroPrime_formula piece chooseRecipe point r t.2 F gap choice J w y he]

end Hindman168
