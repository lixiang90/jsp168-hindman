import Hindman168.UnitCircleStrongLinearRecurrence

namespace Hindman168
open scoped Classical

theorem real_power_bound_from_fractional_length (τ t N β B : ℝ) (e : ℕ)
    (hτ : 0 < τ) (hN : 0 ≤ N) (hβ : 0 ≤ β) (ht : τ*N ≤ t)
    (hbound : t^e*β ≤ B) : N^e*β ≤ B/τ^e := by
  have hpow := pow_le_pow_left₀ (mul_nonneg hτ.le hN) ht e
  have hmul := (mul_le_mul_of_nonneg_right hpow hβ).trans hbound
  rw [mul_pow] at hmul
  apply (le_div_iff₀ (pow_pos hτ e)).mpr
  nlinarith only [hmul]

/-- The genuine strong linear recurrence improves actual dense multiple
errors C/N^e to C/N^(e+1). All bounds precede x and N. -/
theorem unit_circle_dense_multiple_power_inverse (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (e : ℕ) (he : 0 < e) (C : ℝ) (hC : 0 < C) :
    ∃ A M : ℕ, 0 < A ∧ 0 < M ∧ ∀ (x : ℝ) (N : ℕ), M ≤ N →
      δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n : ℕ =>
        ‖(((n : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ C/(N : ℝ)^e)).card →
      ∃ q : ℕ, 0 < q ∧ q ≤ A ∧
        (N : ℝ)^(e+1)*‖(((q : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)*C := by
  obtain ⟨K, hK, hinv⟩ := unit_circle_strong_linear_recurrence δ hδ hδ1
  let A := K+⌈16*(K : ℝ)/δ⌉₊+1
  let M := ⌈10*C/δ⌉₊+⌈8*(K : ℝ)/δ⌉₊+1
  have hA : 0 < A := by dsimp only [A]; omega
  have hM : 0 < M := by dsimp only [M]; omega
  have hKA : K ≤ A := by dsimp only [A]; omega
  have hbound : 16*(K : ℝ)/δ ≤ A := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈16*(K : ℝ)/δ⌉₊ ≤ A by dsimp only [A]; omega))
  have hM10 : 10*C/δ ≤ M := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈10*C/δ⌉₊ ≤ M by dsimp only [M]; omega))
  have hM8 : 8*(K : ℝ)/δ ≤ M := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈8*(K : ℝ)/δ⌉₊ ≤ M by dsimp only [M]; omega))
  refine ⟨A, M, hA, hM, ?_⟩
  intro x N hMN hdense
  have hN : 0 < N := hM.trans_le hMN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hMNr : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hNpow : (N : ℝ) ≤ (N : ℝ)^e := le_self_pow₀ hNr1 he.ne'
  have hεsmall : C/(N : ℝ)^e ≤ δ/10 := by
    apply (div_le_iff₀ (pow_pos hNr e)).mpr
    have hbase := (div_le_iff₀ hδ).mp (hM10.trans hMNr)
    have hpowδ := mul_le_mul_of_nonneg_left hNpow hδ.le
    nlinarith
  have hlarge : 8*(K : ℝ) ≤ δ*(N : ℝ) := by
    have hb := (div_le_iff₀ hδ).mp (hM8.trans hMNr)
    nlinarith
  have hdense' : δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n : ℕ =>
      ‖((0+(n : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ C/(N : ℝ)^e)).card := by
    simpa only [zero_add] using hdense
  obtain ⟨q, hq, hqK, href⟩ := hinv x 0 N hN (C/(N : ℝ)^e)
    (by positivity) hεsmall hlarge hdense'
  have hmul := mul_le_mul_of_nonneg_left href (pow_nonneg hNr.le e)
  have heq : (N : ℝ)^e*(16*(K : ℝ)*(C/(N : ℝ)^e)/δ) = (16*(K : ℝ)/δ)*C := by
    field_simp
  have hlhs : (N : ℝ)^e*((N : ℝ)*‖(((q : ℝ)*x : ℝ) : UnitAddCircle)‖) =
      (N : ℝ)^(e+1)*‖(((q : ℝ)*x : ℝ) : UnitAddCircle)‖ := by rw [pow_succ]; ring
  rw [heq, hlhs] at hmul
  exact ⟨q, hq, hqK.trans hKA, hmul.trans (mul_le_mul_of_nonneg_right hbound hC.le)⟩

end Hindman168
