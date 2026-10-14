import Hindman168.UnitCircleAffineSmallValueInverse

/-! SAME dense original samples with N-scaled affine small values yield
true N^2 slope and N offset bounds, with fixed budgets before ALL sources. -/
namespace Hindman168
open scoped Classical

theorem unit_circle_dense_scaled_affine_inverse (δ B : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B) :
    ∃ A T : ℕ, 0 < A ∧ 0 < T ∧ ∀ (α β : ℝ) (N : ℕ), T ≤ N →
      δ*(N : ℝ) ≤ ((Finset.range N).filter (fun h : ℕ =>
        (N : ℝ)*‖((β+α*(h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ B)).card →
      ∃ r : ℕ, 0 < r ∧ r ≤ A ∧
        (N : ℝ)^2*‖(((r : ℝ)*α : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)*B ∧
        (N : ℝ)*‖(((r : ℝ)*β : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)*B := by
  obtain ⟨A,hA,hinv⟩ := unit_circle_affine_small_value_inverse δ hδ hδ1
  let T := A+⌈10*B/δ⌉₊+1
  have hT : 0 < T := by dsimp only [T]; omega
  refine ⟨A,T,hA,hT,?_⟩
  intro α β N hTN hdense
  have hN : 0 < N := hT.trans_le hTN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hAN : A ≤ N := (show A ≤ T by dsimp only [T]; omega).trans hTN
  have hlarge : 10*B/δ ≤ (N : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast ((show ⌈10*B/δ⌉₊ ≤ T by dsimp only [T]; omega).trans hTN))
  have hε : B/(N : ℝ) ≤ δ/10 := by
    have hh := (div_le_iff₀ hδ).mp hlarge
    apply (div_le_iff₀ hn).mpr
    nlinarith
  have hfilters : ((Finset.range N).filter (fun h : ℕ =>
      (N : ℝ)*‖((β+α*(h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ B)) ⊆
      (Finset.range N).filter (fun h : ℕ => ‖((β+(h : ℝ)*α : ℝ) : UnitAddCircle)‖ ≤ B/(N : ℝ)) := by
    intro h hh
    obtain ⟨hRange,hsmall⟩ := Finset.mem_filter.mp hh
    exact Finset.mem_filter.mpr ⟨hRange,(le_div_iff₀ hn).mpr (by simpa only [mul_comm α,mul_comm (N : ℝ)] using hsmall)⟩
  have hcount := hdense.trans (show _ ≤ (((Finset.range N).filter (fun h : ℕ =>
      ‖((β+(h : ℝ)*α : ℝ) : UnitAddCircle)‖ ≤ B/(N : ℝ))).card : ℝ) by exact_mod_cast Finset.card_le_card hfilters)
  obtain ⟨r,hr,hrA,hslope,hoffset⟩ := hinv α β N hAN _ (by positivity) hε hcount
  have hS := mul_le_mul_of_nonneg_left hslope hn.le
  have hO := mul_le_mul_of_nonneg_left hoffset hn.le
  have he : (N : ℝ)*((A : ℝ)*(B/(N : ℝ)))=(A : ℝ)*B := by field_simp
  refine ⟨r,hr,hrA,?_,?_⟩
  · nlinarith [he]
  · exact hO.trans he.le

theorem unit_circle_affine_completed_bound (α β : ℝ) (N h : ℕ) (A : ℝ)
    (hh : h ≤ N) (hβ : (N : ℝ)*‖(β : UnitAddCircle)‖ ≤ A)
    (hα : (N : ℝ)^2*‖(α : UnitAddCircle)‖ ≤ A) :
    (N : ℝ)*‖((β+α*(h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ 2*A := by
  have hStep := mod_one_natural_multiplier_norm_le h α
  have hTriangle : ‖((β+α*(h : ℝ) : ℝ) : UnitAddCircle)‖ ≤
      ‖(β : UnitAddCircle)‖+(h : ℝ)*‖(α : UnitAddCircle)‖ := by
    calc
      _ ≤ ‖(β : UnitAddCircle)‖+‖((α*(h : ℝ) : ℝ) : UnitAddCircle)‖ := by
        simpa only [AddCircle.coe_add] using norm_add_le (β : UnitAddCircle) ((α*(h : ℝ) : ℝ) : UnitAddCircle)
      _ ≤ _ := add_le_add le_rfl (show ‖((α*(h : ℝ) : ℝ) : UnitAddCircle)‖ ≤
        (h : ℝ)*‖(α : UnitAddCircle)‖ by simpa only [mul_comm α] using hStep)
  have hH : (h : ℝ) ≤ N := by exact_mod_cast hh
  have hS : (N : ℝ)*(h : ℝ)*‖(α : UnitAddCircle)‖ ≤ (N : ℝ)^2*‖(α : UnitAddCircle)‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hH (norm_nonneg (α : UnitAddCircle)),
      (show (0 : ℝ) ≤ N from Nat.cast_nonneg N)]
  have hT := mul_le_mul_of_nonneg_left hTriangle (Nat.cast_nonneg N)
  nlinarith

end Hindman168
