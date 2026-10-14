import Hindman168.SubgroupDualStability

namespace Hindman168
open scoped BigOperators Classical

theorem finiteHaarMean_centered_sample_sum {A : Type*} [Fintype A] [Nonempty A]
    (h : A → ℝ) (hz : finiteHaarMean h = 0) (m : ℕ) :
    finiteHaarMean (fun s : Fin m → A => ∑ j, h (s j)) = 0 ∧
    finiteHaarMean (fun s : Fin m → A => (∑ j, h (s j)) ^ 2) =
      m * finiteHaarMean (fun a => h a ^ 2) := by
  induction m with
  | zero => simp only [Fin.sum_univ_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      finiteHaarMean_const, Nat.cast_zero, zero_mul, and_self]
  | succ m ih =>
    constructor
    · rw [finiteHaarMean_fin_succ]
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, finiteHaarMean_add,
        finiteHaarMean_const, ih.1, add_zero, hz]
    · rw [finiteHaarMean_fin_succ]
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have he (a : A) (s : Fin m → A) :
          (h a + ∑ j, h (s j)) ^ 2 = h a ^ 2 + 2 * h a * (∑ j, h (s j)) + (∑ j, h (s j)) ^ 2 := by ring
      simp_rw [he]
      simp only [finiteHaarMean_add, finiteHaarMean_const, finiteHaarMean_const_mul,
        ih.1, ih.2, mul_zero, add_zero, Nat.cast_add, Nat.cast_one]
      ring

theorem finiteHaarMean_centered_variance {A : Type*} [Fintype A] [Nonempty A] (h : A → ℝ) :
    finiteHaarMean (fun a => (h a - finiteHaarMean h) ^ 2) =
      finiteHaarMean (fun a => h a ^ 2) - finiteHaarMean h ^ 2 := by
  have he (a : A) : (h a - finiteHaarMean h) ^ 2 =
      h a ^ 2 - 2 * finiteHaarMean h * h a + finiteHaarMean h ^ 2 := by ring
  simp_rw [he]
  rw [finiteHaarMean_add, finiteHaarMean_sub, finiteHaarMean_const_mul, finiteHaarMean_const]
  ring

theorem finiteHaarMean_sample_variance {A : Type*} [Fintype A] [Nonempty A]
    (h : A → ℝ) (m : ℕ) (hm : 0 < m) :
    finiteHaarMean (fun s : Fin m → A => ((∑ j, h (s j)) / m - finiteHaarMean h) ^ 2) =
      (finiteHaarMean (fun a => h a ^ 2) - finiteHaarMean h ^ 2) / m := by
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hz : finiteHaarMean (fun a => h a - finiteHaarMean h) = 0 := by
    rw [finiteHaarMean_sub, finiteHaarMean_const, sub_self]
  have hs := (finiteHaarMean_centered_sample_sum _ hz m).2
  have he (s : Fin m → A) : ((∑ j, h (s j)) / m - finiteHaarMean h) ^ 2 =
      (m : ℝ)⁻¹ ^ 2 * (∑ j, (h (s j) - finiteHaarMean h)) ^ 2 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp_rw [he]
  rw [finiteHaarMean_const_mul, hs, finiteHaarMean_centered_variance]
  field_simp

theorem finiteHaarMean_exists_le {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    ∃ a, f a ≤ finiteHaarMean f := by
  by_contra hn
  have ha : ∀ a, finiteHaarMean f < f a := by simpa only [not_exists, not_le] using hn
  have hs := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty)
    (fun a _ => ha a)
  have hc : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have he := div_lt_div_of_pos_right hs hc
  change finiteHaarMean (fun _ : A => finiteHaarMean f) < finiteHaarMean f at he
  rw [finiteHaarMean_const] at he
  exact (lt_irrefl _) he

theorem finiteHaarMean_exists_sample_L2 {A X : Type*} [Fintype A] [Nonempty A]
    [Fintype X] [Nonempty X] (F : A → X → ℝ) (hF : ∀ a x, |F a x| ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    ∃ s : Fin m → A, finiteHaarMean (fun x =>
      ((∑ j, F (s j) x) / m - finiteHaarMean (fun a => F a x)) ^ 2) ≤ 1 / (m : ℝ) := by
  have hb (x : X) : finiteHaarMean (fun s : Fin m → A =>
      ((∑ j, F (s j) x) / m - finiteHaarMean (fun a => F a x)) ^ 2) ≤ 1 / (m : ℝ) := by
    rw [finiteHaarMean_sample_variance (fun a => F a x) m hm]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
    have he : finiteHaarMean (fun a => F a x ^ 2) ≤ 1 := by
      calc
        _ ≤ finiteHaarMean (fun _ : A => (1 : ℝ)) := finiteHaarMean_mono _ _ (fun a => by
          have ha := hF a x
          have hn := abs_nonneg (F a x)
          have he := sq_abs (F a x)
          nlinarith)
        _ = _ := finiteHaarMean_const _
    nlinarith [sq_nonneg (finiteHaarMean (fun a => F a x))]
  obtain ⟨s, hs⟩ := finiteHaarMean_exists_le (fun s : Fin m → A => finiteHaarMean (fun x =>
    ((∑ j, F (s j) x) / m - finiteHaarMean (fun a => F a x)) ^ 2))
  refine ⟨s, hs.trans ?_⟩
  rw [finiteHaarMean_comm]
  exact (finiteHaarMean_mono _ _ hb).trans_eq (finiteHaarMean_const _)

theorem subgroupDualFunction_exists_sample_L2 {G : Type*} [AddCommGroup G] [Fintype G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (f : G → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    ∃ s : Fin m → (Fin d → Q), finiteHaarMean (fun x =>
      ((∑ j, ∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
        f (x + ∑ k ∈ ω, (s j k : G))) / m - subgroupDualFunction Q d f x) ^ 2) ≤ 1 / (m : ℝ) := by
  refine finiteHaarMean_exists_sample_L2 (fun (a : Fin d → Q) (x : G) =>
    ∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅, f (x + ∑ k ∈ ω, (a k : G))) ?_ m hm
  intro a x
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => hf _)

end Hindman168
