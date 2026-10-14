import Hindman168.UniformGroupProbability
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith

/-!
# Actual uniform unit residue laws and quotient projections

Units are sampled uniformly as a finite group, then coerced into ZMod.
Every positive divisor quotient preserves this law by the proved equal-
fiber group theorem and mathlib's actual surjective units reduction.
For prime powers the unit coefficient is at most twice the full-residue
coefficient, uniformly in the exponent (including exponent zero).
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def zmodUnitUniformMass (q : ℕ) [NeZero q] : Mass (ZMod q) :=
  (uniformFintypeMass (ZMod q)ˣ).mapDomain (fun u : (ZMod q)ˣ => (u : ZMod q))

theorem zmodUnitUniformMass_apply (q : ℕ) [NeZero q] (a : ZMod q) :
    zmodUnitUniformMass q a = if IsUnit a then (q.totient : ℝ)⁻¹ else 0 := by
  unfold zmodUnitUniformMass
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [if_pos u.isUnit, Finsupp.mapDomain_apply Units.val_injective,
      uniformFintypeMass_apply, ZMod.card_units_eq_totient]
  · rw [if_neg ha]
    apply Finsupp.mapDomain_of_not_mem_image_support
    rintro ⟨u, _, hu⟩
    exact ha (hu ▸ u.isUnit)

theorem zmodUnitUniformMass_nonneg (q : ℕ) [NeZero q] (a : ZMod q) :
    0 ≤ zmodUnitUniformMass q a :=
  push_nonneg (uniformFintypeMass (ZMod q)ˣ) (fun u : (ZMod q)ˣ => (u : ZMod q))
    (uniformFintypeMass_nonneg _) a

theorem zmodUnitUniformMass_total (q : ℕ) [NeZero q] : total (zmodUnitUniformMass q) = 1 := by
  rw [zmodUnitUniformMass, total_push, uniformFintypeMass_total]

theorem zmodUnitUniformMass_quotient {Q q : ℕ} [NeZero Q] [NeZero q] (h : q ∣ Q) :
    (zmodUnitUniformMass Q).mapDomain (ZMod.castHom h (ZMod q)) = zmodUnitUniformMass q := by
  unfold zmodUnitUniformMass
  rw [← Finsupp.mapDomain_comp]
  have heq : (ZMod.castHom h (ZMod q)) ∘ (fun u : (ZMod Q)ˣ => (u : ZMod Q)) =
      (fun u : (ZMod q)ˣ => (u : ZMod q)) ∘ ZMod.unitsMap h := by funext u; rfl
  rw [heq, Finsupp.mapDomain_comp,
    uniformFintypeMass_group_push (ZMod.unitsMap h) (ZMod.unitsMap_surjective h)]

theorem prime_power_le_twice_totient {p : ℕ} (hp : p.Prime) (e : ℕ) :
    p ^ e ≤ 2 * (p ^ e).totient := by
  cases e with
  | zero => simp
  | succ e =>
    have h : p ≤ 2 * (p - 1) := by have := hp.two_le; omega
    calc
      p ^ (e + 1) = p ^ e * p := Nat.pow_succ p e
      _ ≤ p ^ e * (2 * (p - 1)) := Nat.mul_le_mul_left _ h
      _ = 2 * (p ^ (e + 1)).totient := by rw [Nat.totient_prime_pow_succ hp]; ring

theorem zmodPrimePowerUnits_pointwise_le {p : ℕ} [Fact p.Prime] (hp : p.Prime) (e : ℕ) (a : ZMod (p ^ e)) :
    zmodUnitUniformMass (p ^ e) a ≤ 2 * uniformFintypeMass (ZMod (p ^ e)) a := by
  letI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  rw [zmodUnitUniformMass_apply, uniformFintypeMass_apply, ZMod.card]
  by_cases ha : IsUnit a
  · rw [if_pos ha]
    have hφ : (0 : ℝ) < (p ^ e).totient := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pow_pos hp.pos)
    have hq : (0 : ℝ) < p ^ e := by exact_mod_cast Nat.pow_pos hp.pos
    have hratio : (p ^ e : ℝ) ≤ 2 * ((p ^ e).totient : ℝ) := by
      exact_mod_cast prime_power_le_twice_totient hp e
    have h : (1 : ℝ) / (p ^ e).totient ≤ 2 / (p ^ e : ℝ) :=
      (div_le_div_iff₀ hφ hq).mpr (by simpa only [one_mul] using hratio)
    simpa only [one_div, div_eq_mul_inv, one_mul, Nat.cast_pow] using h
  · rw [if_neg ha]
    positivity

theorem zmodPrimePowerUnits_event_le {p : ℕ} [Fact p.Prime] (hp : p.Prime) (e n : ℕ)
    (E : (Fin n → ZMod (p ^ e)) → Prop) :
    event (piMass (fun _ : Fin n => zmodUnitUniformMass (p ^ e))) E ≤
      (2 : ℝ) ^ n * event (piMass (fun _ : Fin n => uniformFintypeMass (ZMod (p ^ e)))) E := by
  letI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  simpa only [Fintype.card_fin] using event_piMass_domination
    (fun _ : Fin n => zmodUnitUniformMass (p ^ e)) (fun _ => uniformFintypeMass (ZMod (p ^ e)))
    (fun _ => zmodUnitUniformMass_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    (fun _ => zmodPrimePowerUnits_pointwise_le hp e) E

end Hindman168
