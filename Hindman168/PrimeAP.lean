import PrimeNumberTheoremAnd.Consequences
import Hindman168.PrimePool

/-!
# The verified AP-PNT input and its dyadic log-weighted consequences

The prime-number theorem in progressions is credited to PNT+; see
PNTPLUS-ATTRIBUTION.txt. These consequences fix the modulus first.
They do not yet assert equidistribution of the 1/p-weighted pool law.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology

noncomputable def primeLogPrefix (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, if p % q = a then Real.log p else 0

theorem primeLogPrefix_equivalent {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) :
    (primeLogPrefix q a) ~[atTop] (fun x => x / q.totient) :=
  chebyshev_asymptotic_pnt hq ha haq

theorem primeLogPrefix_div_tendsto {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) :
    Tendsto (fun x : ℝ => primeLogPrefix q a x / x) atTop (𝓝 (1 / q.totient)) := by
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have he := primeLogPrefix_equivalent hq ha haq
  have hratio := (isEquivalent_iff_tendsto_one (show
    ∀ᶠ x : ℝ in atTop, x / (q.totient : ℝ) ≠ 0 from
      (eventually_gt_atTop 0).mono (fun x hx => div_ne_zero hx.ne' hφ))).mp he
  have ht := hratio.div_const (q.totient : ℝ)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  dsimp
  field_simp

noncomputable def primeLogDyadicSlice (q a n : ℕ) : ℝ :=
  primeLogPrefix q a (2 ^ (n + 1) : ℕ) - primeLogPrefix q a (2 ^ n : ℕ)

theorem primeLogDyadicSlice_div_tendsto {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) :
    Tendsto (fun n : ℕ => primeLogDyadicSlice q a n / (2 ^ n : ℕ)) atTop
      (𝓝 (1 / q.totient)) := by
  have ht := (primeLogPrefix_div_tendsto hq ha haq).comp
    ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp dyadic_atTop)
  have hnext := ht.comp (tendsto_add_atTop_nat 1)
  have hlim := (hnext.const_mul 2).sub ht
  have hval : (2 : ℝ) * (1 / q.totient) - 1 / q.totient = 1 / q.totient := by ring
  rw [hval] at hlim
  apply hlim.congr
  intro n
  simp only [Function.comp_apply, primeLogDyadicSlice, Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

theorem primeLogDyadicSlice_eventually_pos {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) :
    ∀ᶠ n in atTop, 0 < primeLogDyadicSlice q a n := by
  have hp : (0 : ℝ) < 1 / q.totient := one_div_pos.mpr (by
    exact_mod_cast Nat.totient_pos.mpr hq)
  have ht := primeLogDyadicSlice_div_tendsto hq ha haq
  filter_upwards [ht.eventually (eventually_gt_nhds hp)] with n hn
  exact (div_pos_iff_of_pos_right (by
    exact_mod_cast Nat.pow_pos (by decide : 0 < 2))).mp hn

theorem primeLogDyadicSlice_uniform {q : ℕ} (A : Finset ℕ) (hq : 1 ≤ q)
    (hA : ∀ a ∈ A, a.Coprime q ∧ a < q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ a ∈ A,
      |primeLogDyadicSlice q a n / (2 ^ n : ℕ) - 1 / q.totient| < ε := by
  apply (eventually_all_finset A).mpr
  intro a ha
  have ht := primeLogDyadicSlice_div_tendsto hq (hA a ha).1 (hA a ha).2
  have hlo := ht.eventually (eventually_gt_nhds (show 1 / (q.totient : ℝ) - ε <
    1 / q.totient by linarith))
  have hhi := ht.eventually (eventually_lt_nhds (show 1 / (q.totient : ℝ) <
    1 / q.totient + ε by linarith))
  filter_upwards [hlo, hhi] with n hnlo hnhi
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end Hindman168
