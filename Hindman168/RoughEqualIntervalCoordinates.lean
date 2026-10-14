import Hindman168.RoughEqualIntervalTiling

namespace Hindman168
open scoped Classical

theorem rough_equal_interval_coordinate_quotient (a : ℤ) (N r : ℕ)
    (hN : 0 < N) (x : ℤ)
    (hx : x ∈ Finset.Ico (a+(N*r : ℕ)) (a+(N*(r+1) : ℕ))) :
    (x-a).toNat/N = r := by
  have hx' := Finset.mem_Ico.mp hx
  let k := (x-a).toNat
  have ha : a ≤ x := by
    have hh : (0 : ℤ) ≤ (N*r : ℕ) := by positivity
    omega
  have hkZ : (k : ℤ) = x-a := Int.toNat_of_nonneg (sub_nonneg.mpr ha)
  have hlo : N*r ≤ k := by
    have h : ((N*r : ℕ) : ℤ) ≤ k := by omega
    exact_mod_cast h
  have hhi : k < N*(r+1) := by
    have h : (k : ℤ) < ((N*(r+1) : ℕ) : ℤ) := by omega
    exact_mod_cast h
  have hl : r ≤ k/N := (Nat.le_div_iff_mul_le hN).mpr (by nlinarith)
  have hu : k/N < r+1 := (Nat.div_lt_iff_lt_mul hN).mpr (by nlinarith)
  change k/N = r
  omega

theorem rough_equal_interval_tiled_coordinate_iff (a : ℤ) (width N r : ℕ)
    (hN : 0 < N) (hr : r < width/N) (x : ℤ) :
    (x ∈ Finset.Ico a (a+(N*(width/N) : ℕ)) ∧ (x-a).toNat/N = r) ↔
      x ∈ Finset.Ico (a+(N*r : ℕ)) (a+(N*(r+1) : ℕ)) := by
  constructor
  · rintro ⟨hx, hquot⟩
    have hx' := Finset.mem_Ico.mp hx
    let k := (x-a).toNat
    have hkZ : (k : ℤ) = x-a := Int.toNat_of_nonneg (by omega)
    have hkquot : k/N = r := hquot
    have hm : k%N+N*r = k := by simpa only [hkquot] using Nat.mod_add_div k N
    have hmod := Nat.mod_lt k hN
    have hlo : N*r ≤ k := by omega
    have hhi : k < N*(r+1) := by nlinarith
    have hloZ : ((N*r : ℕ) : ℤ) ≤ k := by exact_mod_cast hlo
    have hhiZ : (k : ℤ) < ((N*(r+1) : ℕ) : ℤ) := by exact_mod_cast hhi
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro hx
    refine ⟨?_, rough_equal_interval_coordinate_quotient a N r hN x hx⟩
    have hx' := Finset.mem_Ico.mp hx
    have hmul := Nat.mul_le_mul_left N (Nat.succ_le_of_lt hr)
    have hmulZ : ((N*(r+1) : ℕ) : ℤ) ≤ ((N*(width/N) : ℕ) : ℤ) := by exact_mod_cast hmul
    have hnonneg : (0 : ℤ) ≤ (N*r : ℕ) := by positivity
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

theorem rough_equal_interval_point_coordinates (a : ℤ) (N r : ℕ) (x : ℤ)
    (hx : x ∈ Finset.Ico (a+(N*r : ℕ)) (a+(N*(r+1) : ℕ))) :
    ∃ v < N, x = a+(N*r : ℕ)+(v : ℤ) := by
  have hx' := Finset.mem_Ico.mp hx
  let v := (x-(a+(N*r : ℕ))).toNat
  have hvZ : (v : ℤ) = x-(a+(N*r : ℕ)) := Int.toNat_of_nonneg (by omega)
  have hNmul : ((N*(r+1) : ℕ) : ℤ) = ((N*r : ℕ) : ℤ)+N := by
    push_cast
    ring
  have hv : v < N := by
    have h : (v : ℤ) < N := by omega
    exact_mod_cast h
  exact ⟨v, hv, by omega⟩

end Hindman168
