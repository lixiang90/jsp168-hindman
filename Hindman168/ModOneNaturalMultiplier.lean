import Hindman168.IntegerCombinationModOneBound

namespace Hindman168
open scoped BigOperators Classical

theorem mod_one_natural_multiplier_norm_le (M : ℕ) (x : ℝ) :
    ‖(((M : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ)*‖(x : UnitAddCircle)‖ := by
  have h := integer_combination_mod_one_bound (fun _ : Unit => (M : ℤ)) (fun _ : Unit => x)
    ‖(x : UnitAddCircle)‖ (fun _ => le_rfl)
  simpa using h

theorem finite_mod_one_common_multiplier {ρ : Type*} [Fintype ρ]
    (D : ρ → ℕ) (B : ℕ) (hB : 1 ≤ B) (hD : ∀ r, 0 < D r) (hDB : ∀ r, D r ≤ B) :
    ∃ M : ℕ, 0 < M ∧ M ≤ B^(Fintype.card ρ+1) ∧ ∀ r (x eps : ℝ), 0 ≤ eps →
      ‖(((D r : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ)*eps →
      ‖(((M : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ (B^(Fintype.card ρ+1) : ℕ)*eps := by
  let M := ∏ r : ρ, D r
  have hM : 0 < M := Finset.prod_pos (fun r _ => hD r)
  have hMB : M ≤ B^Fintype.card ρ := by
    have h := Finset.prod_le_prod (s := Finset.univ) (fun r _ => Nat.zero_le (D r))
      (fun r _ => hDB r)
    simpa only [Finset.prod_const, Finset.card_univ] using h
  have hBC : B^Fintype.card ρ ≤ B^(Fintype.card ρ+1) :=
    Nat.pow_le_pow_right hB (Nat.le_succ _)
  refine ⟨M, hM, hMB.trans hBC, ?_⟩
  intro r x eps heps hx
  have hdvd : D r ∣ M := Finset.dvd_prod_of_mem _ (Finset.mem_univ r)
  have he : (M : ℝ)*x = ((M/D r : ℕ) : ℝ)*((D r : ℝ)*x) := by
    have h := Nat.div_mul_cancel hdvd
    have hr : ((M/D r : ℕ) : ℝ)*(D r : ℝ) = M := by exact_mod_cast h
    rw [← hr]
    ring
  rw [he]
  calc
    _ ≤ ((M/D r : ℕ) : ℝ)*‖(((D r : ℝ)*x : ℝ) : UnitAddCircle)‖ :=
      mod_one_natural_multiplier_norm_le _ _
    _ ≤ ((M/D r : ℕ) : ℝ)*((B : ℝ)*eps) := mul_le_mul_of_nonneg_left hx (by positivity)
    _ ≤ ((B^Fintype.card ρ : ℕ) : ℝ)*((B : ℝ)*eps) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.div_le_self M (D r)).trans hMB)
        (mul_nonneg (Nat.cast_nonneg B) heps)
    _ = _ := by rw [pow_succ, Nat.cast_mul]; ring

end Hindman168
