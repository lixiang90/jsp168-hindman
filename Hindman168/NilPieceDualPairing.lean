import Hindman168.NilPieceDualApproximation

/-! Exact finite linearity and pairing decay for the original selected
zero-prime duals. The model's existing uniform admissible-input control
applies even when piece assignments and nilorbits vary with the stage. -/

namespace Hindman168
open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {X P : Type*} [TopologicalSpace X] {d L n N K m : ℕ}

omit [TopologicalSpace X] in
theorem finiteMass_weighted_recipe_list_pairing {α β : Type*}
    (μ : Mass α) (e : α → ℝ) (s : List β) (c : β → ℝ) (f : β → α → ℝ) :
    expectation μ (fun y => e y * (s.map (fun t => c t * f t y)).sum) =
      (s.map (fun t => c t * expectation μ (fun y => e y * f t y))).sum := by
  induction s with
  | nil => simp [expectation]
  | cons t s ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, expectation_add, ih]
    congr 1
    rw [← expectation_const_mul]
    apply congrArg (expectation μ)
    funext y
    ring

theorem pieceRecipeZeroDualSum_pairing_formula
    (recipes : Fin L → CornerProductRecipe (CubeVertex d) X)
    (piece : ℤ → P) (chooseRecipe : P → Fin L) (point : P → ℤ → X)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (choice : ℕ → Fin K)
    (J : Fin K → ℕ) (w : ℕ) (μ : Mass ℤ) (e : ℤ → ℝ) :
    expectation μ (fun y => e y *
      pieceRecipeZeroDualSum (n := n) recipes piece chooseRecipe point F gap choice J w y) =
    ∑ r, ((recipes r).map (fun t => t.1 * expectation μ (fun y => e y *
      (originalZeroPrimeTemplate (n := n) d gap choice).dual F J
        (pieceRecipeDualInput piece chooseRecipe point r t.2) w y))).sum := by
  simp only [pieceRecipeZeroDualSum, Finset.mul_sum]
  rw [expectation_finset_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact finiteMass_weighted_recipe_list_pairing μ e (recipes r) Prod.fst _

theorem pieceRecipeZeroDualSum_pairing_bound
    (recipes : Fin L → CornerProductRecipe (CubeVertex d) X)
    (piece : ℤ → P) (chooseRecipe : P → Fin L) (point : P → ℤ → X)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (choice : ℕ → Fin K)
    (J : Fin K → ℕ) (w : ℕ) (μ : Mass ℤ) (e : ℤ → ℝ) (η : ℝ)
    (hp : ∀ r, ∀ t ∈ recipes r, |expectation μ (fun y => e y *
      (originalZeroPrimeTemplate (n := n) d gap choice).dual F J
        (pieceRecipeDualInput piece chooseRecipe point r t.2) w y)| ≤ η) :
    |expectation μ (fun y => e y *
      pieceRecipeZeroDualSum (n := n) recipes piece chooseRecipe point F gap choice J w y)| ≤
      (∑ r, (recipes r).coefficientMass) * η := by
  rw [pieceRecipeZeroDualSum_pairing_formula recipes piece chooseRecipe point F gap choice J w μ e]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r _
  have hbound (s : CornerProductRecipe (CubeVertex d) X)
      (hs : ∀ t ∈ s, |expectation μ (fun y => e y *
        (originalZeroPrimeTemplate (n := n) d gap choice).dual F J
          (pieceRecipeDualInput piece chooseRecipe point r t.2) w y)| ≤ η) :
      |(s.map (fun t => t.1 * expectation μ (fun y => e y *
        (originalZeroPrimeTemplate (n := n) d gap choice).dual F J
          (pieceRecipeDualInput piece chooseRecipe point r t.2) w y))).sum| ≤
        s.coefficientMass * η := by
    induction s with
    | nil => simp [CornerProductRecipe.coefficientMass]
    | cons t s ih =>
      simp only [List.map_cons, List.sum_cons, CornerProductRecipe.coefficientMass, add_mul]
      apply (abs_add_le _ _).trans
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hs t (by simp)) (abs_nonneg _)
      · exact ih (fun u hu => hs u (by simp [hu]))
  exact hbound (recipes r) (hp r)

theorem pieceRecipeZeroDualSum_pairing_tendsto_zero
    (recipes : Fin L → CornerProductRecipe (CubeVertex d) X)
    (hb : ∀ r, CornerProductRecipe.Bounded (recipes r))
    (piece : ℕ → ℤ → P) (chooseRecipe : ℕ → P → Fin L) (point : ℕ → P → ℤ → X)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (choice : ℕ → Fin K)
    (J : Fin K → ℕ) (C : ℕ → Chain m) (label : ℕ → Fin m)
    (μ : ℕ → Mass ℤ) (e : ℕ → ℤ → ℝ)
    (hν : ∀ᶠ w in atTop, ∀ y, 0 ≤ masterPredictionBlockMask F C label w y)
    (hdual : ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
      ∀ u : OriginalSingleDualInput 0 d, u.Admissible F C label w →
        |expectation (μ w) (fun y => e w y *
          (originalZeroPrimeTemplate (n := n) d gap choice).dual F J u w y)| < η) :
    Tendsto (fun w => expectation (μ w) (fun y => e w y *
      pieceRecipeZeroDualSum (n := n) recipes (piece w) (chooseRecipe w) (point w) F gap choice J w y))
      atTop (𝓝 0) := by
  let A : ℝ := ∑ r, (recipes r).coefficientMass
  have hA : 0 ≤ A := Finset.sum_nonneg (fun r _ => cornerRecipe_coefficientMass_nonneg (recipes r))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε / (A + 1) := div_pos hε (by linarith)
  filter_upwards [hν, hdual (ε / (A + 1)) he] with w hn hd
  rw [Real.dist_eq, sub_zero]
  have h := pieceRecipeZeroDualSum_pairing_bound (n := n) recipes (piece w) (chooseRecipe w) (point w)
    F gap choice J w (μ w) (e w) (ε / (A + 1)) (fun r t ht =>
      (hd _ (pieceRecipeDualInput_admissible (piece w) (chooseRecipe w) (point w) r t.2
        (hb r t ht) F C label w hn)).le)
  apply h.trans_lt
  change A * (ε / (A + 1)) < ε
  have hid : (A + 1) * (ε / (A + 1)) = ε := by field_simp
  nlinarith

end Hindman168
