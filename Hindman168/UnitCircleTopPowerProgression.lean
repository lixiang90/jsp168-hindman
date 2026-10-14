import Hindman168.UnitCirclePhaseVariation
import Hindman168.NormalizedNaturalPowerVariation

namespace Hindman168

/-- Actual variation of a nearly rational top power on an actual integer
progression. Integer divisibility removes the true rational phase exactly. -/
theorem unit_circle_top_power_progression_variation (α B : ℝ) (d N a q j H : ℕ)
    (hN : 0 < N) (hq : 0 < q) (hj : j < H) (ha : a < N) (hn : a+q*j < N)
    (htop : (N : ℝ)^d*‖(((q : ℝ)*α : ℝ) : UnitAddCircle)‖ ≤ B) :
    ‖(AddCircle.toCircle (((α*(a+q*j : ℕ)^d : ℝ)) : UnitAddCircle) : ℂ)-
      (AddCircle.toCircle (((α*(a : ℝ)^d : ℝ)) : UnitAddCircle) : ℂ)‖ ≤
        2*Real.pi*(d : ℝ)*B*(H : ℝ)/(N : ℝ) := by
  let n := a+q*j
  let m := round ((q : ℝ)*α)
  let e := ((q : ℝ)*α-(m : ℝ))/(q : ℝ)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hnar : (n : ℝ) ≤ N := by exact_mod_cast hn.le
  have haar : (a : ℝ) ≤ N := by exact_mod_cast ha.le
  obtain ⟨k, hk⟩ := natural_progression_power_divisible a q j d
  have hkr : (n : ℝ)^d-(a : ℝ)^d = (q : ℝ)*(k : ℝ) := by
    have he := congrArg (fun z : ℤ => (z : ℝ)) hk
    push_cast at he
    simpa only [n, Nat.cast_add, Nat.cast_mul] using he
  have heq : α*((n : ℝ)^d-(a : ℝ)^d)-((m*k : ℤ) : ℝ) =
      e*((n : ℝ)^d-(a : ℝ)^d) := by
    rw [hkr]
    simp only [Int.cast_mul]
    dsimp only [e]
    field_simp
  have hcircle : ((α*((n : ℝ)^d-(a : ℝ)^d) : ℝ) : UnitAddCircle) =
      ((e*((n : ℝ)^d-(a : ℝ)^d) : ℝ) : UnitAddCircle) := by
    rw [← heq, unit_circle_integer_translate]
  have heabs : |e| *(N : ℝ)^d*(q : ℝ) = |(q : ℝ)*α-(m : ℝ)| *(N : ℝ)^d := by
    dsimp only [e]
    rw [abs_div, abs_of_pos hqr]
    field_simp
  have hsmall : |e| *(N : ℝ)^d*(q : ℝ) ≤ B := by
    rw [heabs]
    rw [UnitAddCircle.norm_eq] at htop
    dsimp only [m]
    nlinarith only [htop]
  have hdist : |(n : ℝ)-(a : ℝ)| ≤ (q : ℝ)*(H : ℝ) := by
    have hjr : (j : ℝ) ≤ H := by exact_mod_cast hj.le
    have he : (n : ℝ)-(a : ℝ) = (q : ℝ)*(j : ℝ) := by dsimp only [n]; push_cast; ring
    rw [he, abs_mul, abs_of_pos hqr, abs_of_nonneg (Nat.cast_nonneg j)]
    exact mul_le_mul_of_nonneg_left hjr hqr.le
  have hp := normalized_real_power_variation (n : ℝ) (a : ℝ) (N : ℝ)
    ((q : ℝ)*(H : ℝ)) d hNr (by positivity)
    (by rwa [abs_of_nonneg (Nat.cast_nonneg n)])
    (by rwa [abs_of_nonneg (Nat.cast_nonneg a)]) hdist
  have herr : |e*((n : ℝ)^d-(a : ℝ)^d)| ≤ (d : ℝ)*B*(H : ℝ)/(N : ℝ) := by
    rw [abs_mul]
    calc
      _ ≤ |e| *((d : ℝ)*((q : ℝ)*(H : ℝ)/(N : ℝ))*(N : ℝ)^d) :=
        mul_le_mul_of_nonneg_left hp (abs_nonneg e)
      _ = ((d : ℝ)*(H : ℝ)/(N : ℝ))*(|e| *(N : ℝ)^d*(q : ℝ)) := by ring
      _ ≤ ((d : ℝ)*(H : ℝ)/(N : ℝ))*B :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := by ring
  rw [unit_circle_phase_difference_distance]
  have harg : α*(a+q*j : ℕ)^d-α*(a : ℝ)^d = α*((n : ℝ)^d-(a : ℝ)^d) := by
    change α*(n : ℝ)^d-α*(a : ℝ)^d = _
    ring
  rw [harg, hcircle]
  exact (unit_circle_phase_distance_upper _).trans (by
    have hh := mul_le_mul_of_nonneg_left herr (by positivity : 0 ≤ 2*Real.pi)
    have he : 2*Real.pi*((d : ℝ)*B*(H : ℝ)/(N : ℝ)) =
        2*Real.pi*(d : ℝ)*B*(H : ℝ)/(N : ℝ) := by ring
    rwa [he] at hh)

end Hindman168

