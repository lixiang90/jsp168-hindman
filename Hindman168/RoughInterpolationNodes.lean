import Hindman168.RoughInterpolationDenominator

namespace Hindman168

def roughInterpolationStep (q H : ℕ) : ℕ := (H - 1) / q

def roughInterpolationNode (q H : ℕ) (j : Fin (q + 1)) : ℕ :=
  j.val * roughInterpolationStep q H

theorem roughInterpolationStep_pos {q H : ℕ} (hq : 0 < q) (hH : 2 * q + 2 ≤ H) :
    0 < roughInterpolationStep q H := by
  apply Nat.div_pos (by omega) hq

theorem roughInterpolationNode_bounds {q H : ℕ} (hH : 0 < H) (j : Fin (q + 1)) :
    roughInterpolationNode q H j < H := by
  have h : j.val * ((H - 1) / q) ≤ q * ((H - 1) / q) := by
    gcongr
    exact Nat.le_of_lt_succ j.isLt
  have hdiv := Nat.mul_div_le (H - 1) q
  dsimp only [roughInterpolationNode, roughInterpolationStep]
  omega

theorem roughInterpolationNode_injective {q H : ℕ} (hq : 0 < q) (hH : 2 * q + 2 ≤ H) :
    Function.Injective (roughInterpolationNode q H) := by
  intro j k h
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_right (roughInterpolationStep_pos hq hH) h

theorem roughInterpolationStep_coverage {q H : ℕ} (hq : 0 < q) (hH : 2 * q + 2 ≤ H) :
    H - 1 ≤ 2 * q * roughInterpolationStep q H := by
  have hd := Nat.mod_add_div (H - 1) q
  have hr := Nat.mod_lt (H - 1) hq
  have hp := roughInterpolationStep_pos hq hH
  dsimp only [roughInterpolationStep] at hp ⊢
  nlinarith

theorem roughInterpolationNode_separation {q H : ℕ} (hq : 0 < q) (hH : 2 * q + 2 ≤ H)
    (j k : Fin (q + 1)) (hjk : j < k) :
    ((H - 1 : ℕ) : ℝ) / (2 * q) ≤
      (roughInterpolationNode q H k : ℝ) - roughInterpolationNode q H j := by
  have hd := roughInterpolationStep_coverage hq hH
  have hstep : roughInterpolationStep q H ≤ roughInterpolationNode q H k - roughInterpolationNode q H j := by
    have hj : j.val + 1 ≤ k.val := hjk
    have hm := Nat.mul_le_mul_right (roughInterpolationStep q H) hj
    rw [Nat.add_mul, Nat.one_mul] at hm
    dsimp only [roughInterpolationNode]
    omega
  have hdiff : roughInterpolationNode q H j ≤ roughInterpolationNode q H k := by
    dsimp only [roughInterpolationNode]
    exact Nat.mul_le_mul_right _ (Nat.le_of_lt hjk)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mpr
  have hcast : ((H - 1 : ℕ) : ℝ) ≤ 2 * q * (roughInterpolationStep q H : ℝ) := by exact_mod_cast hd
  have hsc : (roughInterpolationStep q H : ℝ) ≤
      (roughInterpolationNode q H k : ℝ) - roughInterpolationNode q H j := by
    have hs : (roughInterpolationStep q H : ℝ) ≤
        ((roughInterpolationNode q H k - roughInterpolationNode q H j : ℕ) : ℝ) := by exact_mod_cast hstep
    rwa [Nat.cast_sub hdiff] at hs
  nlinarith

theorem roughInterpolationStep_scaled_interval {q H : ℕ} (hq : 0 < q) (hH : 2 * q + 2 ≤ H)
    {z : ℝ} (hz : 0 ≤ z) (hzH : z ≤ ((H - 1 : ℕ) : ℝ)) :
    0 ≤ z / roughInterpolationStep q H ∧ z / roughInterpolationStep q H ≤ 2 * q := by
  have hp : (0 : ℝ) < roughInterpolationStep q H := by exact_mod_cast roughInterpolationStep_pos hq hH
  refine ⟨div_nonneg hz hp.le, (div_le_iff₀ hp).mpr ?_⟩
  apply hzH.trans
  exact_mod_cast roughInterpolationStep_coverage hq hH

end Hindman168
