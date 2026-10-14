import Hindman168.RoughForwardDifferences

namespace Hindman168
open scoped fwdDiff BigOperators

theorem rough_fwdDiff_high_zero {G : Type*} [AddCommGroup G]
    (f : ℕ → G) (q H : ℕ)
    (h : ∀ z, z + q + 1 < H → (Δ_[1]^[q + 1] f) z = 0)
    (n : ℕ) (hn : q + 1 ≤ n) (z : ℕ) (hz : z + n < H) :
    (Δ_[1]^[n] f) z = 0 := by
  induction n generalizing z with
  | zero => omega
  | succ n ih =>
    by_cases he : n = q
    · subst n
      exact h z (by omega)
    · have hqn : q + 1 ≤ n := by omega
      rw [Function.iterate_succ_apply', fwdDiff, ih hqn (z + 1) (by omega), ih hqn z (by omega), sub_self]

theorem rough_finite_newton_formula {G : Type*} [AddCommGroup G]
    (f : ℕ → G) (q H : ℕ)
    (h : ∀ z, z + q + 1 < H → (Δ_[1]^[q + 1] f) z = 0)
    (z : ℕ) (hz : z < H) :
    f z = ∑ k ∈ Finset.range (q + 1), z.choose k • (Δ_[1]^[k] f) 0 := by
  let F : ℕ → G := fun k => z.choose k • (Δ_[1]^[k] f) 0
  let N := max q z
  have hzs : (∑ k ∈ Finset.range (z + 1), F k) = ∑ k ∈ Finset.range (N + 1), F k := by
    apply Finset.sum_subset (Finset.range_mono (by dsimp [N]; omega))
    intro k _ hnot
    have hk : z < k := by simp only [Finset.mem_range] at hnot; omega
    simp only [F, Nat.choose_eq_zero_of_lt hk, zero_nsmul]
  have hqs : (∑ k ∈ Finset.range (q + 1), F k) = ∑ k ∈ Finset.range (N + 1), F k := by
    apply Finset.sum_subset (Finset.range_mono (by dsimp [N]; omega))
    intro k _ hnot
    have hk : q + 1 ≤ k := by simpa only [Finset.mem_range, not_lt] using hnot
    by_cases hzk : z < k
    · simp only [F, Nat.choose_eq_zero_of_lt hzk, zero_nsmul]
    · have hzero := rough_fwdDiff_high_zero f q H h k hk 0 (by omega)
      simp only [F, hzero, smul_zero]
  calc
    f z = ∑ k ∈ Finset.range (z + 1), F k := by
      simpa [F] using shift_eq_sum_fwdDiff_iter (1 : ℕ) f z 0
    _ = ∑ k ∈ Finset.range (N + 1), F k := hzs
    _ = _ := hqs.symm

end Hindman168
