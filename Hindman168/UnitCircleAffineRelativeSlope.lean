import Hindman168.UnitCircleAffineSmallValueInverse

/-! Dense actual affine small values plus the actual initial N^-1 absolute
slope bound force a TRUE slope bound relative to the coefficient size w.
The natural threshold and real budget precede all source values. -/
namespace Hindman168
open scoped Classical

theorem unit_circle_affine_relative_slope (δ A0 B : ℝ) (D : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA0 : 0 ≤ A0) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 0 < T ∧
      ∀ (α β w : ℝ), 0 ≤ w → ∀ N : ℕ, T ≤ N → (N : ℝ)*|α| ≤ A0 → B ≤ (N : ℝ)*w →
        δ*(N : ℝ) ≤ ((Finset.range N).filter (fun h : ℕ =>
          ‖((β+α*(h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ B/(N : ℝ)+(D : ℝ)*w)).card →
          (N : ℝ)*|α| ≤ C*w := by
  obtain ⟨A,hA,hinv⟩ := unit_circle_affine_small_value_inverse δ hδ hδ1
  let T := A+⌈2*(A : ℝ)*A0⌉₊+⌈20*B/δ⌉₊+1
  let C := (A : ℝ)*(D+1 : ℕ)+20*(D : ℝ)*A0/δ+1
  have hT : 0 < T := by dsimp only [T]; omega
  have hc2 : 0 ≤ 20*(D : ℝ)*A0/δ := by positivity
  have hC1 : (A : ℝ)*(D+1 : ℕ) ≤ C := by dsimp only [C]; linarith
  have hC2 : 20*(D : ℝ)*A0/δ ≤ C := by
    have hh : 0 ≤ (A : ℝ)*(D+1 : ℕ) := by positivity
    dsimp only [C]
    linarith
  refine ⟨C,by dsimp only [C]; positivity,T,hT,?_⟩
  intro α β w hw N hTN hα hBw hdense
  have hN : 0 < N := hT.trans_le hTN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hAN : A ≤ N := (show A ≤ T by dsimp only [T]; omega).trans hTN
  have h2 : 2*(A : ℝ)*A0 ≤ (N : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast ((show ⌈2*(A : ℝ)*A0⌉₊ ≤ T by dsimp only [T]; omega).trans hTN))
  have h20 : 20*B/δ ≤ (N : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast ((show ⌈20*B/δ⌉₊ ≤ T by dsimp only [T]; omega).trans hTN))
  have hbδ : B/(N : ℝ) ≤ δ/20 := by
    have hh := (div_le_iff₀ hδ).mp h20
    apply (div_le_iff₀ hn).mpr
    nlinarith
  have hε : 0 ≤ B/(N : ℝ)+(D : ℝ)*w := by positivity
  by_cases hsmall : B/(N : ℝ)+(D : ℝ)*w ≤ δ/10
  · obtain ⟨q,hq,hqA,hslope,_⟩ := hinv α β N hAN _ hε hsmall (by
      simpa only [mul_comm α] using hdense)
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hqAr : (q : ℝ) ≤ A := by exact_mod_cast hqA
    have hqa : (N : ℝ)*|(q : ℝ)*α| ≤ (A : ℝ)*A0 := by
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg q)]
      have hh := mul_le_mul_of_nonneg_left hα (Nat.cast_nonneg q)
      have ha := mul_le_mul_of_nonneg_right hqAr hA0
      nlinarith
    have hhalf : |(q : ℝ)*α| ≤ (1 : ℝ)/2 := by nlinarith [hqa,h2]
    have hnorm : ‖(((q : ℝ)*α : ℝ) : UnitAddCircle)‖=|(q : ℝ)*α| :=
      (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr (by simpa only [abs_one] using hhalf)
    rw [hnorm] at hslope
    have hεw : B/(N : ℝ) ≤ w := (div_le_iff₀ hn).mpr (by nlinarith [hBw])
    have hs : (N : ℝ)*|α| ≤ (N : ℝ)*|(q : ℝ)*α| := by
      have heq : |(q : ℝ)*α|=(q : ℝ)*|α| := by
        rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg q)]
      rw [heq]
      have hh := le_mul_of_one_le_left (abs_nonneg α) hqr
      exact mul_le_mul_of_nonneg_left hh hn.le
    calc
      _ ≤ (A : ℝ)*(B/(N : ℝ)+(D : ℝ)*w) := hs.trans hslope
      _ ≤ (A : ℝ)*(w+(D : ℝ)*w) := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg A)
      _ = ((A : ℝ)*(D+1 : ℕ))*w := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC1 hw
  · have hh : δ/10 < B/(N : ℝ)+(D : ℝ)*w := lt_of_not_ge hsmall
    have hd : δ ≤ 20*(D : ℝ)*w := by linarith
    have hm := mul_le_mul_of_nonneg_right hd hA0
    have ha : A0 ≤ (20*(D : ℝ)*A0/δ)*w := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hδ).mpr
      nlinarith
    exact hα.trans (ha.trans (mul_le_mul_of_nonneg_right hC2 hw))

end Hindman168
