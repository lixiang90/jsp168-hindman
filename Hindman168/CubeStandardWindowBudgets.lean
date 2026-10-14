import Hindman168.CubeStandardAlphaBox

/-! Fixed integer/reciprocal budgets contain each fixed alpha window. The
budgets are selected before m and do not impose a diagonal alpha(m). -/
namespace Hindman168

theorem cube_standard_window_budget_bound (d : ℕ) (beta α L c C : ℝ)
    (hL : 0 ≤ L) (hα : 0 ≤ α) (hc : c ≤ α) (hC : |beta|+α ≤ C) :
    ∀ j, |cubeAlphaLower d beta L j| ≤ C*L ∧
      |cubeAlphaUpper d beta L α j| ≤ C*L ∧
      c*L ≤ cubeAlphaUpper d beta L α j-cubeAlphaLower d beta L j := by
  have hl : ∀ j, |cubeAlphaLower d beta L j| ≤ |beta| * L := by
    intro j
    refine Fin.cases ?_ (fun _ => ?_) j
    · simp only [cubeAlphaLower,Fin.cases_zero,abs_mul,abs_of_nonneg hL]
      exact le_rfl
    · simp only [cubeAlphaLower,Fin.cases_succ,abs_zero]
      exact mul_nonneg (abs_nonneg _) hL
  intro j
  have ha : |α*L|=α*L := abs_of_nonneg (mul_nonneg hα hL)
  have hbound : |beta| * L+α*L ≤ C*L := by
    rw [←add_mul]
    exact mul_le_mul_of_nonneg_right hC hL
  refine ⟨(hl j).trans (by linarith [mul_nonneg hα hL]),?_,?_⟩
  · change |cubeAlphaLower d beta L j + α*L| ≤ C*L
    calc
      _ ≤ |cubeAlphaLower d beta L j| + |α*L| := abs_add_le _ _
      _ ≤ |beta| * L + α*L := by
        rw [ha]
        exact add_le_add (hl j) le_rfl
      _ ≤ C*L := hbound
  · simpa only [cubeAlphaUpper,add_sub_cancel_left] using mul_le_mul_of_nonneg_right hc hL

theorem cube_standard_window_integer_budgets (d : ℕ) (beta α : ℝ) (hα : 0 < α) :
    ∃ C c : ℕ, ∀ L : ℝ, 0 ≤ L → ∀ j,
      |cubeAlphaLower d beta L j| ≤ C*L ∧
      |cubeAlphaUpper d beta L α j| ≤ C*L ∧
      (1/(c+1 : ℝ))*L ≤ cubeAlphaUpper d beta L α j-cubeAlphaLower d beta L j := by
  obtain ⟨C,hC⟩ := exists_nat_gt (|beta|+α)
  obtain ⟨c,hc⟩ := exists_nat_one_div_lt hα
  exact ⟨C,c,fun L hL => cube_standard_window_budget_bound d beta α L _ _ hL hα.le hc.le hC.le⟩

end Hindman168
