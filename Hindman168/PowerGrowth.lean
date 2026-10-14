import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Domination of every fixed power and polynomially weighted errors

`PowerDominates F Q` means Q^n = o(F) for every fixed natural n. It is
the growth hypothesis, not a hypothesis that the desired sampling errors
are already small. A polynomial-over-F majorant gives the little-o error
at every inverse-power scale of V, provided 1 <= V <= Q eventually.
-/

namespace Hindman168

open Filter Asymptotics
open scoped Topology

def PowerDominates {α : Type*} (l : Filter α) (F Q : α → ℝ) : Prop :=
  ∀ n : ℕ, (fun w => Q w ^ n) =o[l] F

def RapidlySmall {α : Type*} (l : Filter α) (V e : α → ℝ) : Prop :=
  ∀ C : ℕ, e =o[l] (fun w => (V w ^ C)⁻¹)

theorem PowerDominates.eventually_bound {α : Type*} {l : Filter α}
    {F Q : α → ℝ} (h : PowerDominates l F Q)
    (hF : ∀ᶠ w in l, 0 ≤ F w) (hQ : ∀ᶠ w in l, 0 ≤ Q w)
    (n : ℕ) {A : ℝ} (hA : 0 < A) : ∀ᶠ w in l, A * Q w ^ n ≤ F w := by
  filter_upwards [(h n).bound (inv_pos.mpr hA), hF, hQ] with w hw hFw hQw
  simp only [Real.norm_eq_abs, abs_of_nonneg hFw,
    abs_of_nonneg (pow_nonneg hQw n)] at hw
  have hm := mul_le_mul_of_nonneg_left hw hA.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] using hm

theorem PowerDominates.mono_right {α : Type*} {l : Filter α}
    {F G Q : α → ℝ} (h : PowerDominates l F Q)
    (hFG : ∀ᶠ w in l, 0 ≤ F w ∧ F w ≤ G w) : PowerDominates l G Q := by
  intro n
  apply (h n).trans_isBigO
  apply IsBigO.of_bound 1
  filter_upwards [hFG] with w hw
  simp only [Real.norm_eq_abs, abs_of_nonneg hw.1,
    abs_of_nonneg (hw.1.trans hw.2), one_mul]
  exact hw.2

theorem PowerDominates.mono_base {α : Type*} {l : Filter α}
    {F Q S : α → ℝ} (h : PowerDominates l F S) (d : ℕ)
    (hQS : ∀ᶠ w in l, 0 ≤ Q w ∧ 0 ≤ S w ∧ Q w ≤ S w ^ d) :
    PowerDominates l F Q := by
  intro n
  apply IsBigO.trans_isLittleO (g := fun w => S w ^ (d * n)) _ (h (d * n))
  apply IsBigO.of_bound 1
  filter_upwards [hQS] with w hw
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hw.1 n),
    abs_of_nonneg (pow_nonneg hw.2.1 (d * n)), one_mul]
  rw [pow_mul]
  exact pow_le_pow_left₀ hw.1 hw.2.2 n

/-- A quantitative polynomial-over-growth bound yields every inverse
polynomial little-o scale. The growth condition is used at exponent p+C. -/
theorem rapid_of_polynomial_majorant {α : Type*} {l : Filter α}
    {F Q V e : α → ℝ} (hD : PowerDominates l F Q)
    (hF : ∀ᶠ w in l, 0 < F w)
    (hVQ : ∀ᶠ w in l, 1 ≤ V w ∧ V w ≤ Q w)
    (p : ℕ) {A : ℝ} (hA : 0 < A)
    (he : ∀ᶠ w in l, |e w| ≤ A * Q w ^ p / F w) : RapidlySmall l V e := by
  intro C
  apply isLittleO_iff.mpr
  intro c hc
  filter_upwards [(hD (p + C)).bound (div_pos hc hA), hF, hVQ, he]
    with w hw hFw hVQw hew
  have hV : 0 < V w := lt_of_lt_of_le zero_lt_one hVQw.1
  have hQ : 0 < Q w := hV.trans_le hVQw.2
  have hVP : 0 < V w ^ C := pow_pos hV C
  have hQP : 0 ≤ Q w ^ p := pow_nonneg hQ.le p
  have hpow : V w ^ C ≤ Q w ^ C := pow_le_pow_left₀ hV.le hVQw.2 C
  have hmaj : 0 ≤ A * Q w ^ p / F w := div_nonneg (mul_nonneg hA.le hQP) hFw.le
  simp only [Real.norm_eq_abs, abs_of_pos hFw, abs_of_pos (pow_pos hQ (p + C))] at hw
  have hm : A * Q w ^ (p + C) ≤ c * F w := by
    have ht := mul_le_mul_of_nonneg_left hw hA.le
    have hh : A * (c / A * F w) = c * F w := by field_simp
    rwa [hh] at ht
  have heprod : |e w| * V w ^ C ≤ c := by
    calc
      _ ≤ (A * Q w ^ p / F w) * V w ^ C := mul_le_mul_of_nonneg_right hew hVP.le
      _ ≤ (A * Q w ^ p / F w) * Q w ^ C := mul_le_mul_of_nonneg_left hpow hmaj
      _ = A * Q w ^ (p + C) / F w := by rw [pow_add]; ring
      _ ≤ c := (div_le_iff₀ hFw).mpr hm
  simp only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hVP)]
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ hVP).mpr heprod

theorem RapidlySmall.of_abs_le {α : Type*} {l : Filter α} {V e d : α → ℝ}
    (h : RapidlySmall l V e) (hd : ∀ᶠ w in l, |d w| ≤ |e w|) : RapidlySmall l V d := by
  intro C
  apply isLittleO_iff.mpr
  intro c hc
  filter_upwards [(h C).bound hc, hd] with w hw hdw
  exact hdw.trans hw

/-- Fixed polynomial losses, such as bounded test functions, are absorbed. -/
theorem RapidlySmall.mul_power {α : Type*} {l : Filter α} {V e : α → ℝ}
    (h : RapidlySmall l V e) (hV : ∀ᶠ w in l, 0 < V w) (B : ℕ) :
    RapidlySmall l V (fun w => V w ^ B * e w) := by
  intro C
  apply isLittleO_iff.mpr
  intro c hc
  filter_upwards [(h (C + B)).bound hc, hV] with w hw hVw
  have hp : 0 < V w ^ B := pow_pos hVw B
  simp only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hVw (C + B)))] at hw
  have hm := mul_le_mul_of_nonneg_left hw hp.le
  have he : V w ^ B * (c * (V w ^ (C + B))⁻¹) = c * (V w ^ C)⁻¹ := by
    rw [pow_add]
    field_simp
  rw [he] at hm
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos hp,
    abs_of_pos (inv_pos.mpr (pow_pos hVw C))] using hm

theorem RapidlySmall.const_mul {α : Type*} {l : Filter α} {V e : α → ℝ}
    (h : RapidlySmall l V e) (A : ℝ) : RapidlySmall l V (fun w => A * e w) :=
  fun C => (h C).const_mul_left A

/-- Natural-power rates imply the paper's statement for every fixed real C. -/
theorem RapidlySmall.rpow_scale {α : Type*} {l : Filter α} {V e : α → ℝ}
    (h : RapidlySmall l V e) (hV : ∀ᶠ w in l, 1 ≤ V w) (C : ℝ) :
    e =o[l] (fun w => V w ^ (-C)) := by
  apply (h (Nat.ceil C)).trans_isBigO
  apply IsBigO.of_bound 1
  filter_upwards [hV] with w hw
  have hVp : 0 < V w := lt_of_lt_of_le zero_lt_one hw
  simp only [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hVp.le _)),
    abs_of_pos (Real.rpow_pos_of_pos hVp _), one_mul]
  rw [← Real.rpow_natCast, ← Real.rpow_neg hVp.le]
  exact Real.rpow_le_rpow_of_exponent_le hw (neg_le_neg (Nat.le_ceil C))

end Hindman168
