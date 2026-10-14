import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Hindman168
open scoped BigOperators Classical

theorem finite_range_multiply_sum {M : Type*} [AddCommMonoid M]
    (K L : ℕ) (f : ℕ → M) :
    (∑ n ∈ Finset.range (K*L), f n) =
      ∑ b ∈ Finset.range K, ∑ j ∈ Finset.range L, f (b*L+j) := by
  by_cases hL : L=0
  · simp only [hL, mul_zero, Finset.range_zero, Finset.sum_empty, Finset.sum_const_zero]
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL
  rw [← Finset.sum_product (Finset.range K) (Finset.range L)
    (fun p : ℕ × ℕ => f (p.1*L+p.2))]
  apply Finset.sum_bij' (fun n _ => (n/L,n%L)) (fun p _ => p.1*L+p.2)
  · intro n hn
    have h := Finset.mem_range.mp hn
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hLpos).mpr h),
      Finset.mem_range.mpr (Nat.mod_lt n hLpos)⟩
  · intro p hp
    have h := Finset.mem_product.mp hp
    have hb := Finset.mem_range.mp h.1
    have hj := Finset.mem_range.mp h.2
    apply Finset.mem_range.mpr
    have hmul := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hb)
    nlinarith
  · intro n _
    dsimp
    nlinarith [Nat.mod_add_div n L]
  · intro p hp
    have h := Finset.mem_product.mp hp
    have hj := Finset.mem_range.mp h.2
    apply Prod.ext
    · dsimp
      rw [Nat.add_comm (p.1*L) p.2, Nat.add_mul_div_right _ _ hLpos,
        Nat.div_eq_of_lt hj, zero_add]
    · dsimp
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero, Nat.zero_mod, zero_add,
        Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj]
  · intro n _
    dsimp
    rw [show n/L*L+n%L=n by nlinarith [Nat.mod_add_div n L]]

/-- Actual complete blocks split into their true residue progressions. -/
theorem finite_natural_progression_blocks_sum {M : Type*} [AddCommMonoid M]
    (K q H : ℕ) (f : ℕ → M) :
    (∑ n ∈ Finset.range (q*H*K), f n) =
      ∑ b ∈ Finset.range K, ∑ r ∈ Finset.range q, ∑ j ∈ Finset.range H,
        f (q*H*b+r+q*j) := by
  rw [show q*H*K=K*(H*q) by ring, finite_range_multiply_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [finite_range_multiply_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

theorem natural_progression_block_index_bound (K q H b r j : ℕ)
    (hb : b < K) (hr : r < q) (hj : j < H) : q*H*b+r+q*j < q*H*K := by
  have hmulj := Nat.mul_le_mul_left q (Nat.succ_le_of_lt hj)
  have hmulb := Nat.mul_le_mul_left (q*H) (Nat.succ_le_of_lt hb)
  nlinarith

end Hindman168
