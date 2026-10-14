import Hindman168.PrimePool
import Hindman168.CutoffGrowth
import Hindman168.FiniteTensor

/-!
# Chosen actual dyadic prime pools with power-dominating size and mass

These pools contain all primes in a consecutive union of complete dyadic
intervals. Their lower endpoint exceeds Q, so every prime is a Q-unit.
Their lower endpoint and harmonic mass dominate all fixed powers of V,
and the maximum-atom majorant is rapidly small. Equidistribution modulo
Q is a further requirement, not asserted for this selection.
-/

namespace Hindman168

open Filter
open scoped Topology

structure DyadicPrimePool where
  lowerExponent : ℕ
  upperExponent : ℕ
  increasing : lowerExponent < upperExponent

def DyadicPrimePool.lower (P : DyadicPrimePool) : ℕ := 2 ^ P.lowerExponent
def DyadicPrimePool.upper (P : DyadicPrimePool) : ℕ := 2 ^ P.upperExponent
noncomputable def DyadicPrimePool.harmonicMass (P : DyadicPrimePool) : ℝ :=
  primePoolHarmonicMass P.lower P.upper

theorem exists_dyadicPrimePool (L : ℕ) (H : ℝ) :
    ∃ P : DyadicPrimePool, L ≤ P.lower ∧ H ≤ P.harmonicMass := by
  obtain ⟨a, b, hab, ha, hh⟩ := exists_dyadic_prime_pool L H
  exact ⟨⟨a, b, hab⟩, ha, hh⟩

def primePoolGrowthTarget (V w : ℕ) : ℕ := (w + 1) * (V + 1) ^ w

theorem primePoolGrowthTarget_pos (V w : ℕ) : 0 < primePoolGrowthTarget V w :=
  Nat.mul_pos (by omega) (Nat.pow_pos (by omega))

theorem primePoolGrowthTarget_lower (V w : ℕ) : w * V ^ w ≤ primePoolGrowthTarget V w :=
  Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega : V ≤ V + 1) w)

noncomputable def growingPrimePool (V Q w : ℕ) : DyadicPrimePool :=
  Classical.choose (exists_dyadicPrimePool (max (Q + 1) (primePoolGrowthTarget V w))
    (primePoolGrowthTarget V w : ℝ))

theorem growingPrimePool_bounds (V Q w : ℕ) :
    Q < (growingPrimePool V Q w).lower ∧
      primePoolGrowthTarget V w ≤ (growingPrimePool V Q w).lower ∧
      (primePoolGrowthTarget V w : ℝ) ≤ (growingPrimePool V Q w).harmonicMass := by
  have h := Classical.choose_spec
    (exists_dyadicPrimePool (max (Q + 1) (primePoolGrowthTarget V w))
      (primePoolGrowthTarget V w : ℝ))
  exact ⟨lt_of_lt_of_le (by omega) ((le_max_left _ _).trans h.1),
    (le_max_right _ _).trans h.1, h.2⟩

theorem growingPrimePool_mass_pos (V Q w : ℕ) : 0 < (growingPrimePool V Q w).harmonicMass :=
  lt_of_lt_of_le (by exact_mod_cast primePoolGrowthTarget_pos V w) (growingPrimePool_bounds V Q w).2.2

theorem growingPrimePool_mass_one_le (V Q w : ℕ) : 1 ≤ (growingPrimePool V Q w).harmonicMass := by
  have ht : 1 ≤ primePoolGrowthTarget V w := primePoolGrowthTarget_pos V w
  have hr : (1 : ℝ) ≤ primePoolGrowthTarget V w := by exact_mod_cast ht
  exact hr.trans (growingPrimePool_bounds V Q w).2.2

theorem growingPrimePool_support_units (V Q w : ℕ) {p : ℕ}
    (hp : p ∈ primePool (growingPrimePool V Q w).lower (growingPrimePool V Q w).upper)
    (hQ : 0 < Q) : p.Coprime Q := by
  have hm := primePool_mem.mp hp
  have hpQ : Q < p := (growingPrimePool_bounds V Q w).1.trans_le hm.1
  apply hm.2.2.coprime_iff_not_dvd.mpr
  exact fun hd => (Nat.le_of_dvd hQ hd).not_gt hpQ

theorem growingPrimePool_lower_powerDominates {V Q : ℕ → ℕ}
    (hV : ∀ᶠ w in atTop, 1 ≤ V w) :
    PowerDominates atTop (fun w => ((growingPrimePool (V w) (Q w) w).lower : ℝ))
      (fun w => (V w : ℝ)) := by
  apply powerDominates_of_parameter_power
    (hV.mono (fun _ hw => by exact_mod_cast hw))
  exact Eventually.of_forall (fun w => by
    exact_mod_cast (primePoolGrowthTarget_lower (V w) w).trans
      (growingPrimePool_bounds (V w) (Q w) w).2.1)

theorem growingPrimePool_mass_powerDominates {V Q : ℕ → ℕ}
    (hV : ∀ᶠ w in atTop, 1 ≤ V w) :
    PowerDominates atTop (fun w => (growingPrimePool (V w) (Q w) w).harmonicMass)
      (fun w => (V w : ℝ)) := by
  apply powerDominates_of_parameter_power
    (hV.mono (fun _ hw => by exact_mod_cast hw))
  exact Eventually.of_forall (fun w => by
    have ht : (w : ℝ) * (V w : ℝ) ^ w ≤ primePoolGrowthTarget (V w) w := by
      exact_mod_cast primePoolGrowthTarget_lower (V w) w
    exact ht.trans (growingPrimePool_bounds (V w) (Q w) w).2.2)

theorem growingPrimePool_atom_cap_rapid {V Q : ℕ → ℕ}
    (hV : ∀ᶠ w in atTop, 1 ≤ V w) :
    RapidlySmall atTop (fun w => (V w : ℝ)) (fun w =>
      1 / (((growingPrimePool (V w) (Q w) w).lower : ℝ) *
        (growingPrimePool (V w) (Q w) w).harmonicMass)) := by
  have hLower (w : ℕ) : (0 : ℝ) < (growingPrimePool (V w) (Q w) w).lower := by
    exact_mod_cast Nat.pow_pos (by decide : 0 < 2)
  apply rapid_of_polynomial_majorant (growingPrimePool_lower_powerDominates hV)
    (Eventually.of_forall hLower) (hV.mono (fun _ hw => ⟨by exact_mod_cast hw, le_rfl⟩))
    0 (by norm_num : (0 : ℝ) < 1)
  apply Eventually.of_forall
  intro w
  have hH := growingPrimePool_mass_one_le (V w) (Q w) w
  have hp := growingPrimePool_mass_pos (V w) (Q w) w
  rw [abs_of_pos (div_pos zero_lt_one (mul_pos (hLower w) hp))]
  simp only [pow_zero, mul_one]
  exact one_div_le_one_div_of_le (hLower w) (by nlinarith [hLower w])

theorem growingPrimePool_atom_rapid {V Q p : ℕ → ℕ}
    (hV : ∀ᶠ w in atTop, 1 ≤ V w) :
    RapidlySmall atTop (fun w => (V w : ℝ)) (fun w =>
      primePoolMass (growingPrimePool (V w) (Q w) w).lower
        (growingPrimePool (V w) (Q w) w).upper (p w)) := by
  apply (growingPrimePool_atom_cap_rapid hV).of_abs_le
  apply Eventually.of_forall
  intro w
  rw [abs_of_nonneg (primePoolMass_nonneg _ _ _)]
  exact (primePool_max_atom (Nat.pow_pos (by decide : 0 < 2))
    (growingPrimePool_mass_pos (V w) (Q w) w) (p w)).trans (le_abs_self _)

end Hindman168
