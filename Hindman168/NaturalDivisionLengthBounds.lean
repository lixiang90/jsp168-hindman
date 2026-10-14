import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Genuine floor division length has a fixed positive retained proportion.
The integer remainder is retained; no real division is substituted for floor. -/
namespace Hindman168

theorem natural_division_length_lower (N k : ℕ) (hk : 0 < k) (hNk : k ≤ N) :
    (N : ℝ)/((2*k : ℕ) : ℝ) ≤ (N/k : ℕ) := by
  have hH : 1 ≤ N/k := Nat.div_pos hNk hk
  have hMod : N%k ≤ k := (Nat.mod_lt N hk).le
  have hkH : k ≤ (N/k)*k := by
    simpa only [one_mul] using Nat.mul_le_mul_right k hH
  have hN : N ≤ (2*k)*(N/k) := by
    calc
      _ = (N/k)*k+N%k := by simpa only [Nat.mul_comm] using (Nat.div_add_mod N k).symm
      _ ≤ (N/k)*k+k := Nat.add_le_add_left hMod _
      _ ≤ (N/k)*k+(N/k)*k := Nat.add_le_add_left hkH _
      _ = _ := by ring
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((2*k : ℕ) : ℝ))).mpr
  exact_mod_cast (show N ≤ (N/k)*(2*k) by simpa only [Nat.mul_comm] using hN)

end Hindman168
