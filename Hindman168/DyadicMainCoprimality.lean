import Hindman168.DyadicCoprimalityControls

/-!
# Combining both exposed-main orientations

Actual full controls for the two smaller polynomial pairs close the
recurrence when both main endpoints are maximal in their own tuples.
Both possible endpoint orders are handled with exact tuple swapping.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem dyadic_recurrence_error_absorb (a b c d w L : ℕ)
    (hL : Real.exp 2 ≤ (L : ℝ)) :
    (a : ℝ) * dyadicCoprimeError w L + (b : ℝ) * dyadicCoprimeError w L +
      (c : ℝ) / w + (d : ℝ) * (Real.log (L : ℝ) / Real.sqrt L) ≤
      (a + b + c + d : ℕ) * dyadicCoprimeError w L := by
  have hLone : 1 ≤ (L : ℝ) :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).le.trans hL
  have hx : 0 ≤ 1 / (w : ℝ) := one_div_nonneg.mpr (Nat.cast_nonneg w)
  have hy : 0 ≤ Real.log (L : ℝ) / Real.sqrt L :=
    div_nonneg (Real.log_nonneg hLone) (Real.sqrt_nonneg _)
  have hcx := mul_nonneg (Nat.cast_nonneg c) hy
  have hdy := mul_nonneg (Nat.cast_nonneg d) hx
  unfold dyadicCoprimeError
  simp only [Nat.cast_add, div_eq_mul_inv, one_mul] at hcx hdy ⊢
  nlinarith only [hcx, hdy]

theorem exists_dyadic_main_control_of_lower_controls {m n : ℕ}
    {F : MvPolynomial (Fin (m + 1)) ℤ} {G : MvPolynomial (Fin (n + 1)) ℤ}
    (hF : F ≠ 0) (hG : G ≠ 0)
    (hAFG : ∃ w0 e0 K : ℕ,
      DyadicCoprimeControl (integerPolynomialMainLeading F) G w0 e0 K)
    (hFAG : ∃ w0 e0 K : ℕ,
      DyadicCoprimeControl F (integerPolynomialMainLeading G) w0 e0 K) :
    ∃ w0 e0 K : ℕ, DyadicMainCoprimeControl F G w0 e0 K := by
  obtain ⟨w1, e1, K1, h1⟩ := hAFG
  obtain ⟨w2, e2, K2, h2⟩ := hFAG
  obtain ⟨r1, hr1⟩ := exists_dyadic_common_prime_recurrence hF hG
  obtain ⟨r2, hr2⟩ := exists_dyadic_common_prime_recurrence hG hF
  let w0 := max w1 w2
  let e0 := max e1 (max e2 (max r1 r2))
  let c1 := dyadicRecurrenceSmall F G
  let d1 := dyadicRecurrenceLarge F G
  let c2 := dyadicRecurrenceSmall G F
  let d2 := dyadicRecurrenceLarge G F
  let K := K1 + K2 + c1 + d1 + c2 + d2
  have h1' : DyadicCoprimeControl (integerPolynomialMainLeading F) G w0 e0 K1 :=
    dyadicCoprimeControl_mono h1 (le_max_left _ _) (le_max_left _ _) le_rfl
  have h2' : DyadicCoprimeControl F (integerPolynomialMainLeading G) w0 e0 K2 :=
    dyadicCoprimeControl_mono h2 (le_max_right _ _)
      ((le_max_left _ _).trans (le_max_right _ _)) le_rfl
  have hR1 : r1 ≤ e0 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hR2 : r2 ≤ e0 :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hK1 : K1 + K2 + c1 + d1 ≤ K := by dsimp [K]; omega
  have hK2 : K2 + K1 + c2 + d2 ≤ K := by dsimp [K]; omega
  refine ⟨w0, e0, K, ?_⟩
  intro eF eG heF heG hmaxF hmaxG w L hww hw hL hLF hLG
  have hleft := h1' (fun i => eF i.succ) eG (fun i => heF i.succ) heG
    w L hww hw hL (fun i => hLF i.succ) hLG
  have hright := h2' eF (fun i => eG i.succ) heF (fun i => heG i.succ)
    w L hww hw hL hLF (fun i => hLG i.succ)
  by_cases horder : eF 0 ≤ eG 0
  · have hr := hr1 eF eG (fun i => hR1.trans (heF i)) (fun i => hR1.trans (heG i))
      hmaxF horder w L hw hL hLF hLG
    calc
      dyadicCommonPrimeMass eF eG w F G ≤
          dyadicCommonPrimeMass (fun i => eF i.succ) eG w (integerPolynomialMainLeading F) G +
          dyadicCommonPrimeMass eF (fun i => eG i.succ) w F (integerPolynomialMainLeading G) +
          (c1 : ℝ) / w + (d1 : ℝ) * (Real.log (L : ℝ) / Real.sqrt L) := hr
      _ ≤ (K1 : ℝ) * dyadicCoprimeError w L + (K2 : ℝ) * dyadicCoprimeError w L +
          (c1 : ℝ) / w + (d1 : ℝ) * (Real.log (L : ℝ) / Real.sqrt L) := by
        linarith only [hleft, hright]
      _ ≤ (K1 + K2 + c1 + d1 : ℕ) * dyadicCoprimeError w L :=
        dyadic_recurrence_error_absorb K1 K2 c1 d1 w L hL
      _ ≤ (K : ℝ) * dyadicCoprimeError w L :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hK1) (dyadicCoprimeError_nonneg hL)
  · have hr := hr2 eG eF (fun i => hR2.trans (heG i)) (fun i => hR2.trans (heF i))
      hmaxG (le_of_not_ge horder) w L hw hL hLG hLF
    rw [dyadicCommonPrimeMass_swap eF eG F G,
      dyadicCommonPrimeMass_swap eF (fun i => eG i.succ) F (integerPolynomialMainLeading G),
      dyadicCommonPrimeMass_swap (fun i => eF i.succ) eG (integerPolynomialMainLeading F) G] at hr
    calc
      dyadicCommonPrimeMass eF eG w F G ≤
          dyadicCommonPrimeMass eF (fun i => eG i.succ) w F (integerPolynomialMainLeading G) +
          dyadicCommonPrimeMass (fun i => eF i.succ) eG w (integerPolynomialMainLeading F) G +
          (c2 : ℝ) / w + (d2 : ℝ) * (Real.log (L : ℝ) / Real.sqrt L) := hr
      _ ≤ (K2 : ℝ) * dyadicCoprimeError w L + (K1 : ℝ) * dyadicCoprimeError w L +
          (c2 : ℝ) / w + (d2 : ℝ) * (Real.log (L : ℝ) / Real.sqrt L) := by
        linarith only [hleft, hright]
      _ ≤ (K2 + K1 + c2 + d2 : ℕ) * dyadicCoprimeError w L :=
        dyadic_recurrence_error_absorb K2 K1 c2 d2 w L hL
      _ ≤ (K : ℝ) * dyadicCoprimeError w L :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hK2) (dyadicCoprimeError_nonneg hL)

end Hindman168
