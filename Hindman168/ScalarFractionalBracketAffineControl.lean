import Hindman168.ScalarFractionalBracket
import Hindman168.UnitCircleAffineRelativeSlope

/-! ACTUAL bracket hits imply genuine affine hits and relative slope bound,
with finite coordinate budget and SAME original N. -/
namespace Hindman168
open scoped BigOperators Classical

theorem scalar_fractional_bracket_affine_norm {ι : Type*} [Fintype ι]
    (β α : ℝ) (ζ γ : ι → ℝ) (w ε h : ℝ) (hw : ∀ i, |ζ i| ≤ w)
    (hsmall : ‖(scalarFractionalBracket β α ζ γ h : UnitAddCircle)‖ ≤ ε) :
    ‖((β+α*h : ℝ) : UnitAddCircle)‖ ≤ ε+(Fintype.card ι : ℝ)*w := by
  let b := ∑ i, ζ i*Int.fract (h*γ i)
  have hb : |b| ≤ (Fintype.card ι : ℝ)*w := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have hs : (∑ i, |ζ i*Int.fract (h*γ i)|) ≤ ∑ _i : ι, w := by
      apply Finset.sum_le_sum
      intro i _
      have hfr : |Int.fract (h*γ i)|=Int.fract (h*γ i) := abs_of_nonneg (Int.fract_nonneg _)
      rw [abs_mul,hfr]
      exact (mul_le_of_le_one_right (abs_nonneg _) (Int.fract_lt_one _).le).trans (hw i)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hs
  have hb' : ‖(b : UnitAddCircle)‖ ≤ |b| := (rough_mod_one_near_integer_iff _ _).mpr ⟨0,by simp⟩
  have he : β+α*h=scalarFractionalBracket β α ζ γ h-b := by dsimp only [scalarFractionalBracket,b]; ring
  calc
    _ = ‖(scalarFractionalBracket β α ζ γ h : UnitAddCircle)-(b : UnitAddCircle)‖ := by rw [← AddCircle.coe_sub,← he]
    _ ≤ _ := (norm_sub_le _ _).trans (add_le_add hsmall (hb'.trans hb))

theorem scalar_fractional_bracket_relative_slope (ι : Type*) [Fintype ι]
    (δ A0 B : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA0 : 0 ≤ A0) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 0 < T ∧ ∀ (β α : ℝ) (ζ γ : ι → ℝ) (w : ℝ),
      0 ≤ w → (∀ i, |ζ i| ≤ w) → ∀ N : ℕ, T ≤ N → (N : ℝ)*|α| ≤ A0 → B ≤ (N : ℝ)*w →
        δ*(N : ℝ) ≤ ((Finset.range N).filter (fun h : ℕ =>
          (N : ℝ)*‖(scalarFractionalBracket β α ζ γ (h : ℝ) : UnitAddCircle)‖ ≤ B)).card →
          (N : ℝ)*|α| ≤ C*w := by
  obtain ⟨C,hC,T,hT,hinv⟩ := unit_circle_affine_relative_slope δ A0 B (Fintype.card ι) hδ hδ1 hA0 hB
  refine ⟨C,hC,T,hT,?_⟩
  intro β α ζ γ w hw hζ N hTN hα hBw hdense
  have hN : 0 < N := hT.trans_le hTN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hsub : ((Finset.range N).filter (fun h : ℕ =>
      (N : ℝ)*‖(scalarFractionalBracket β α ζ γ (h : ℝ) : UnitAddCircle)‖ ≤ B)) ⊆
      (Finset.range N).filter (fun h : ℕ =>
        ‖((β+α*(h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ B/(N : ℝ)+(Fintype.card ι : ℝ)*w) := by
    intro h hh
    obtain ⟨hr,hsmall⟩ := Finset.mem_filter.mp hh
    exact Finset.mem_filter.mpr ⟨hr,scalar_fractional_bracket_affine_norm β α ζ γ w _ (h : ℝ) hζ
      ((le_div_iff₀' hn).mpr hsmall)⟩
  exact hinv α β w hw N hTN hα hBw (hdense.trans (by exact_mod_cast Finset.card_le_card hsub))

end Hindman168
