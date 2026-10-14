import Hindman168.RoughFixedInterpolationBound

namespace Hindman168
open Polynomial
open scoped BigOperators Classical

noncomputable def roughScaledInterpolation (q : ℕ) (h : ℝ)
    (values : Fin (q + 1) → ℝ) : ℝ[X] :=
  (Lagrange.interpolate Finset.univ (fun i : Fin (q + 1) => (i.val : ℝ)) values).comp (C h⁻¹ * X)

theorem roughScaledInterpolation_degree (q : ℕ) (h : ℝ) (values : Fin (q + 1) → ℝ) :
    (roughScaledInterpolation q h values).natDegree ≤ q := by
  have hinj : Set.InjOn (fun i : Fin (q + 1) => (i.val : ℝ)) (Finset.univ : Finset (Fin (q + 1))) := by
    intro i _ j _ he
    change (i.val : ℝ) = (j.val : ℝ) at he
    apply Fin.ext
    exact_mod_cast he
  have hd : (Lagrange.interpolate Finset.univ (fun i : Fin (q + 1) => (i.val : ℝ)) values).natDegree ≤ q := by
    apply natDegree_le_of_degree_le
    simpa only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel] using
      Lagrange.degree_interpolate_le values hinj
  apply natDegree_comp_le.trans
  have hc : (C h⁻¹ * X : ℝ[X]).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans natDegree_X_le
  exact (Nat.mul_le_mul hd hc).trans (by simp)

theorem roughScaledInterpolation_eval_node (q : ℕ) (h : ℝ) (hh : h ≠ 0)
    (values : Fin (q + 1) → ℝ) (i : Fin (q + 1)) :
    (roughScaledInterpolation q h values).eval ((i.val : ℝ) * h) = values i := by
  unfold roughScaledInterpolation
  rw [eval_comp, eval_mul, eval_C, eval_X]
  have he : h⁻¹ * ((i.val : ℝ) * h) = i.val := by field_simp
  rw [he]
  apply Lagrange.eval_interpolate_at_node values _ (Finset.mem_univ i)
  intro j _ k _ he
  change (j.val : ℝ) = (k.val : ℝ) at he
  apply Fin.ext
  exact_mod_cast he

theorem roughScaledInterpolation_reproduce (q : ℕ) (h : ℝ) (hh : h ≠ 0)
    (T : ℝ[X]) (hT : T.natDegree ≤ q) :
    roughScaledInterpolation q h (fun i => T.eval ((i.val : ℝ) * h)) = T := by
  have hinj : Set.InjOn (fun i : Fin (q + 1) => (i.val : ℝ) * h) (Finset.univ : Finset (Fin (q + 1))) := by
    intro i _ j _ he
    change (i.val : ℝ) * h = (j.val : ℝ) * h at he
    have hi := mul_right_cancel₀ hh he
    apply Fin.ext
    exact_mod_cast hi
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hinj
  · apply (degree_le_of_natDegree_le (roughScaledInterpolation_degree q h _)).trans_lt
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_lt]
    exact_mod_cast Nat.lt_succ_self q
  · apply (degree_le_of_natDegree_le hT).trans_lt
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_lt]
    exact_mod_cast Nat.lt_succ_self q
  · intro i _
    exact roughScaledInterpolation_eval_node q h hh _ i

theorem roughScaledInterpolation_sub (q : ℕ) (h : ℝ) (a b : Fin (q + 1) → ℝ) :
    roughScaledInterpolation q h (a - b) = roughScaledInterpolation q h a - roughScaledInterpolation q h b := by
  simp only [roughScaledInterpolation, map_sub, sub_comp]

theorem rough_iterate_derivative_scale (P : ℝ[X]) (c : ℝ) (j : ℕ) :
    derivative^[j] (P.comp (C c * X)) = C (c ^ j) * (derivative^[j] P).comp (C c * X) := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, map_one, one_mul]
  | succ j ih =>
    simp only [Function.iterate_succ_apply', ih, derivative_C_mul, derivative_comp,
      derivative_X, mul_one, pow_succ, map_mul, mul_assoc]

theorem roughScaledInterpolation_derivative_bound (q j : ℕ) (hj : j ≤ q)
    (h : ℝ) (hh : 1 ≤ h) (values : Fin (q + 1) → ℝ)
    (eps : ℝ) (heps : 0 ≤ eps) (hv : ∀ i, |values i| ≤ eps)
    (B x : ℝ) (hB : 1 ≤ B) (hx : |x / h| ≤ B) :
    |(derivative^[j] (roughScaledInterpolation q h values)).eval x| ≤
      eps * roughFixedInterpolationMass q * B ^ q := by
  have hp : 0 < h := by linarith
  have hi : h⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hh
  have hb := rough_fixed_interpolation_derivative_bound q j hj values eps heps hv B (x / h) hB hx
  rw [roughScaledInterpolation, rough_iterate_derivative_scale, eval_mul, eval_C, eval_comp,
    eval_mul, eval_C, eval_X, abs_mul, abs_pow, abs_of_pos (inv_pos.mpr hp)]
  have harg : h⁻¹ * x = x / h := by ring
  rw [harg]
  calc
    h⁻¹ ^ j * |(derivative^[j] (Lagrange.interpolate Finset.univ
      (fun i : Fin (q + 1) => (i.val : ℝ)) values)).eval (x / h)| ≤
        1 * (eps * roughFixedInterpolationMass q * B ^ q) :=
      mul_le_mul (pow_le_one₀ (inv_nonneg.mpr hp.le) hi) hb (abs_nonneg _) (by norm_num)
    _ = _ := one_mul _

end Hindman168
