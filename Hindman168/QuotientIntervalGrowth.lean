import Hindman168.SquareRootIntervalGrowth

/-!
# Original shift lengths after division by replica moduli

Every-power gap growth survives taking an integer quotient by a
polynomially bounded positive modulus. The square root of that actual
quotient is therefore a concrete admissible auxiliary interval length.
-/

namespace Hindman168

open Filter Asymptotics
open scoped Topology

theorem PowerDominates.nat_div {α : Type*} {l : Filter α}
    {R D : α → ℕ} {Q : α → ℝ}
    (hD : PowerDominates l (fun w => (R w : ℝ)) Q)
    (p : ℕ) (hQ : ∀ᶠ w in l, 2 ≤ Q w)
    (hden : ∀ᶠ w in l, 0 < D w ∧ (D w : ℝ) ≤ Q w ^ p) :
    PowerDominates l (fun w => ((R w / D w : ℕ) : ℝ)) Q := by
  have ht : ∀ᶠ w in l, 0 < R w / D w := by
    filter_upwards [(hD p).bound (by norm_num : (0 : ℝ) < 1 / 2), hQ, hden]
      with w hw hQw hdw
    have hQp := pow_nonneg (by linarith : 0 ≤ Q w) p
    simp only [Real.norm_eq_abs, abs_of_nonneg hQp,
      abs_of_nonneg (Nat.cast_nonneg (R w) : (0 : ℝ) ≤ R w)] at hw
    have hdr : (D w : ℝ) ≤ R w := by linarith
    exact Nat.div_pos (by exact_mod_cast hdr) hdw.1
  intro n
  apply isLittleO_iff.mpr
  intro c hc
  filter_upwards [(hD (p + n)).bound (by positivity : (0 : ℝ) < c / 2),
    hQ, hden, ht] with w hw hQw hdw htw
  have hQpos : 0 < Q w := by linarith
  have hQpn := pow_nonneg hQpos.le (p + n)
  simp only [Real.norm_eq_abs, abs_of_nonneg hQpn,
    abs_of_nonneg (Nat.cast_nonneg (R w) : (0 : ℝ) ≤ R w)] at hw
  have hu : R w < D w * (R w / D w + 1) := Nat.lt_mul_div_succ _ hdw.1
  have hur : (R w : ℝ) ≤ 2 * (D w : ℝ) * ((R w / D w : ℕ) : ℝ) := by
    have hu' : (R w : ℝ) < (D w : ℝ) * (((R w / D w : ℕ) : ℝ) + 1) := by exact_mod_cast hu
    have ht' : (1 : ℝ) ≤ (R w / D w : ℕ) := by exact_mod_cast htw
    have hd' : (0 : ℝ) ≤ D w := Nat.cast_nonneg _
    nlinarith
  have hup : (R w : ℝ) ≤ 2 * Q w ^ p * ((R w / D w : ℕ) : ℝ) := by
    exact hur.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdw.2 (by norm_num)) (Nat.cast_nonneg _))
  have hp : Q w ^ p * Q w ^ n ≤ Q w ^ p * (c * ((R w / D w : ℕ) : ℝ)) := by
    calc
      _ = Q w ^ (p + n) := (pow_add _ _ _).symm
      _ ≤ c / 2 * (R w : ℝ) := hw
      _ ≤ c / 2 * (2 * Q w ^ p * ((R w / D w : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hup (by positivity)
      _ = _ := by ring
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hQpos.le n),
    abs_of_nonneg (Nat.cast_nonneg (R w / D w) : (0 : ℝ) ≤ (R w / D w : ℕ))]
  exact le_of_mul_le_mul_left hp (pow_pos hQpos p)

theorem quotient_sqrt_auxiliary_growth {α : Type*} {l : Filter α}
    {R D : α → ℕ} {Q : α → ℝ}
    (hD : PowerDominates l (fun w => (R w : ℝ)) Q)
    (p : ℕ) (hQ : ∀ᶠ w in l, 2 ≤ Q w)
    (hden : ∀ᶠ w in l, 0 < D w ∧ (D w : ℝ) ≤ Q w ^ p) :
    PowerDominates l (fun w => (Nat.sqrt (R w / D w) : ℝ)) Q :=
  (hD.nat_div p hQ hden).nat_sqrt (hQ.mono (fun _ hw => zero_le_two.trans hw))

end Hindman168
