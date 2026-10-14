import Hindman168.RoughComplexFiberMean

namespace Hindman168
open scoped Classical

theorem rough_equal_interval_tile_contained (a : ℤ) (width N r : ℕ)
    (hr : r < width/N) :
    Finset.Ico (a+(N*r : ℕ)) (a+(N*(r+1) : ℕ)) ⊆ Finset.Ico a (a+width) := by
  have hmul : N*(r+1) ≤ N*(width/N) := Nat.mul_le_mul_left N (Nat.succ_le_of_lt hr)
  have hmod := Nat.mod_add_div width N
  have hbound : N*(r+1) ≤ width := by omega
  have hboundZ : (N*(r+1) : ℕ) ≤ (width : ℤ) := by exact_mod_cast hbound
  intro x hx
  have hx' := Finset.mem_Ico.mp hx
  apply Finset.mem_Ico.mpr
  constructor
  · have hnonneg : (0 : ℤ) ≤ (N*r : ℕ) := by positivity
    omega
  · omega

theorem rough_equal_interval_tile_card (a : ℤ) (N r : ℕ) :
    (Finset.Ico (a+(N*r : ℕ)) (a+(N*(r+1) : ℕ))).card = N := by
  rw [Int.card_Ico]
  have he : (a+(N*(r+1) : ℕ))-(a+(N*r : ℕ)) = (N : ℤ) := by
    push_cast
    ring
  rw [he, Int.toNat_natCast]

theorem rough_equal_interval_tiled_decomposition (a : ℤ) (width N : ℕ)
    (hN : 0 < N) (x : ℤ) :
    x ∈ Finset.Ico a (a+(N*(width/N) : ℕ)) ↔
      ∃ r < width/N, ∃ v < N, x = a+(N*r : ℕ)+(v : ℤ) := by
  constructor
  · intro hx
    have hx' := Finset.mem_Ico.mp hx
    let k := (x-a).toNat
    have hkZ : (k : ℤ) = x-a := Int.toNat_of_nonneg (by omega)
    have hk : k < N*(width/N) := by
      have h : (k : ℤ) < (N*(width/N) : ℕ) := by omega
      exact_mod_cast h
    have hr : k/N < width/N := (Nat.div_lt_iff_lt_mul hN).mpr (by nlinarith)
    refine ⟨k/N, hr, k%N, Nat.mod_lt k hN, ?_⟩
    have hm : ((k%N : ℕ) : ℤ)+((N*(k/N) : ℕ) : ℤ) = (k : ℤ) := by
      exact_mod_cast Nat.mod_add_div k N
    omega
  · rintro ⟨r, hr, v, hv, rfl⟩
    have hmul := Nat.mul_le_mul_left N (Nat.succ_le_of_lt hr)
    have hb : N*r+v < N*(width/N) := by nlinarith
    have hbZ : ((N*r+v : ℕ) : ℤ) < ((N*(width/N) : ℕ) : ℤ) := by exact_mod_cast hb
    have hnonneg : (0 : ℤ) ≤ (N*r : ℕ) := by positivity
    have hv0 : (0 : ℤ) ≤ v := by positivity
    rw [Nat.cast_add] at hbZ
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

theorem rough_equal_interval_boundary_card (a : ℤ) (width N : ℕ) :
    (Finset.Ico a (a+width) \ Finset.Ico a (a+(N*(width/N) : ℕ))).card = width%N := by
  rw [Finset.Ico_sdiff_Ico_left, max_eq_right (le_add_of_nonneg_right (by positivity) : a ≤ a+(N*(width/N) : ℕ)),
    Int.card_Ico]
  have hm : ((width%N : ℕ) : ℤ)+((N*(width/N) : ℕ) : ℤ) = (width : ℤ) := by
    exact_mod_cast Nat.mod_add_div width N
  have he : (a+width)-(a+(N*(width/N) : ℕ)) = ((width%N : ℕ) : ℤ) := by omega
  rw [he, Int.toNat_natCast]

end Hindman168
