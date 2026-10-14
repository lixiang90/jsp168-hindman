import Hindman168.PrimePoolCombine

/-!
# Simultaneously growing and equidistributed actual prime pools

For each parameter, the modulus is fixed before choosing the endpoints.
The lower endpoint and harmonic mass exceed (w+1)(V+1)^w; the L1 residue
error is at most its reciprocal. Thus arbitrary growing moduli are allowed
without asserting a uniform-in-modulus prime-number theorem. Independent
prime slots may use the actual normalized finite pool law.
-/

namespace Hindman168

open Filter
open scoped Topology

noncomputable def equidistributedGrowingPrimePool (V Q w : ℕ) (hQ : 1 ≤ Q) : DyadicPrimePool :=
  Classical.choose (exists_dyadic_equidi_prime_pool hQ (primePoolGrowthTarget V w)
    (primePoolGrowthTarget V w : ℝ) (ε := 1 / (primePoolGrowthTarget V w : ℝ)) (one_div_pos.mpr (by
      exact_mod_cast primePoolGrowthTarget_pos V w)))

theorem equidistributedGrowingPrimePool_bounds (V Q w : ℕ) (hQ : 1 ≤ Q) :
    Q < (equidistributedGrowingPrimePool V Q w hQ).lower ∧
      primePoolGrowthTarget V w ≤ (equidistributedGrowingPrimePool V Q w hQ).lower ∧
      (primePoolGrowthTarget V w : ℝ) ≤ (equidistributedGrowingPrimePool V Q w hQ).harmonicMass ∧
      0 < (equidistributedGrowingPrimePool V Q w hQ).harmonicMass ∧
      FiniteMass.distance (primePoolResidueMass Q
        (equidistributedGrowingPrimePool V Q w hQ).lower
        (equidistributedGrowingPrimePool V Q w hQ).upper) (primeUnitUniformMass Q) ≤
        1 / (primePoolGrowthTarget V w : ℝ) :=
  Classical.choose_spec (exists_dyadic_equidi_prime_pool hQ (primePoolGrowthTarget V w)
    (primePoolGrowthTarget V w : ℝ) (ε := 1 / (primePoolGrowthTarget V w : ℝ)) (one_div_pos.mpr (by
      exact_mod_cast primePoolGrowthTarget_pos V w)))

theorem equidistributedGrowingPrimePool_mass_pos (V Q w : ℕ) (hQ : 1 ≤ Q) :
    0 < (equidistributedGrowingPrimePool V Q w hQ).harmonicMass :=
  (equidistributedGrowingPrimePool_bounds V Q w hQ).2.2.2.1

theorem equidistributedGrowingPrimePool_mass_one_le (V Q w : ℕ) (hQ : 1 ≤ Q) :
    1 ≤ (equidistributedGrowingPrimePool V Q w hQ).harmonicMass := by
  have ht : 1 ≤ primePoolGrowthTarget V w := primePoolGrowthTarget_pos V w
  have hr : (1 : ℝ) ≤ primePoolGrowthTarget V w := by exact_mod_cast ht
  exact hr.trans (equidistributedGrowingPrimePool_bounds V Q w hQ).2.2.1

theorem equidistributedGrowingPrimePool_support_units (V Q w : ℕ) (hQ : 1 ≤ Q) {p : ℕ}
    (hp : p ∈ primePool (equidistributedGrowingPrimePool V Q w hQ).lower
      (equidistributedGrowingPrimePool V Q w hQ).upper) : p.Coprime Q := by
  have hm := primePool_mem.mp hp
  have hpQ : Q < p := (equidistributedGrowingPrimePool_bounds V Q w hQ).1.trans_le hm.1
  exact hm.2.2.coprime_iff_not_dvd.mpr (fun hd => (Nat.le_of_dvd hQ hd).not_gt hpQ)

theorem primePoolGrowthTarget_powerDominates {V : ℕ → ℕ}
    (hV : ∀ᶠ w in atTop, 1 ≤ V w) :
    PowerDominates atTop (fun w => (primePoolGrowthTarget (V w) w : ℝ)) (fun w => (V w : ℝ)) := by
  apply powerDominates_of_parameter_power (hV.mono (fun _ hw => by exact_mod_cast hw))
  exact Eventually.of_forall (fun w => by exact_mod_cast primePoolGrowthTarget_lower (V w) w)

theorem primePoolGrowthTarget_inverse_rapid {V : ℕ → ℕ}
    (hV : ∀ᶠ w in atTop, 1 ≤ V w) :
    RapidlySmall atTop (fun w => (V w : ℝ)) (fun w => 1 / (primePoolGrowthTarget (V w) w : ℝ)) := by
  have hp (w : ℕ) : (0 : ℝ) < primePoolGrowthTarget (V w) w := by
    exact_mod_cast primePoolGrowthTarget_pos (V w) w
  apply rapid_of_polynomial_majorant (primePoolGrowthTarget_powerDominates hV)
    (Eventually.of_forall hp) (hV.mono (fun _ hw => ⟨by exact_mod_cast hw, le_rfl⟩))
    0 (by norm_num : (0 : ℝ) < 1)
  exact Eventually.of_forall (fun w => by
    simp only [abs_of_pos (one_div_pos.mpr (hp w)), pow_zero, mul_one, le_refl])

theorem equidistributedGrowingPrimePool_lower_powerDominates {V Q : ℕ → ℕ}
    (hQ : ∀ w, 1 ≤ Q w) (hV : ∀ᶠ w in atTop, 1 ≤ V w) :
    PowerDominates atTop (fun w =>
      ((equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).lower : ℝ)) (fun w => (V w : ℝ)) := by
  apply powerDominates_of_parameter_power (hV.mono (fun _ hw => by exact_mod_cast hw))
  exact Eventually.of_forall (fun w => by
    exact_mod_cast (primePoolGrowthTarget_lower (V w) w).trans
      (equidistributedGrowingPrimePool_bounds (V w) (Q w) w (hQ w)).2.1)

theorem equidistributedGrowingPrimePool_mass_powerDominates {V Q : ℕ → ℕ}
    (hQ : ∀ w, 1 ≤ Q w) (hV : ∀ᶠ w in atTop, 1 ≤ V w) :
    PowerDominates atTop (fun w =>
      (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).harmonicMass) (fun w => (V w : ℝ)) := by
  apply powerDominates_of_parameter_power (hV.mono (fun _ hw => by exact_mod_cast hw))
  exact Eventually.of_forall (fun w => by
    have ht : (w : ℝ) * (V w : ℝ) ^ w ≤ primePoolGrowthTarget (V w) w := by
      exact_mod_cast primePoolGrowthTarget_lower (V w) w
    exact ht.trans (equidistributedGrowingPrimePool_bounds (V w) (Q w) w (hQ w)).2.2.1)

theorem equidistributedGrowingPrimePool_residue_rapid {V Q : ℕ → ℕ}
    (hQ : ∀ w, 1 ≤ Q w) (hV : ∀ᶠ w in atTop, 1 ≤ V w) :
    RapidlySmall atTop (fun w => (V w : ℝ)) (fun w => FiniteMass.distance
      (primePoolResidueMass (Q w) (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).lower
        (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).upper)
      (primeUnitUniformMass (Q w))) := by
  apply (primePoolGrowthTarget_inverse_rapid hV).of_abs_le
  apply Eventually.of_forall
  intro w
  rw [FiniteMass.distance, abs_of_nonneg (FiniteMass.variation_nonneg _)]
  exact (equidistributedGrowingPrimePool_bounds (V w) (Q w) w (hQ w)).2.2.2.2.trans (le_abs_self _)

theorem equidistributedGrowingPrimePool_atom_cap_rapid {V Q : ℕ → ℕ}
    (hQ : ∀ w, 1 ≤ Q w) (hV : ∀ᶠ w in atTop, 1 ≤ V w) :
    RapidlySmall atTop (fun w => (V w : ℝ)) (fun w =>
      1 / (((equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).lower : ℝ) *
        (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).harmonicMass)) := by
  have hLower (w : ℕ) : (0 : ℝ) < (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).lower := by
    exact_mod_cast Nat.pow_pos (by decide : 0 < 2)
  apply rapid_of_polynomial_majorant (equidistributedGrowingPrimePool_lower_powerDominates hQ hV)
    (Eventually.of_forall hLower) (hV.mono (fun _ hw => ⟨by exact_mod_cast hw, le_rfl⟩))
    0 (by norm_num : (0 : ℝ) < 1)
  apply Eventually.of_forall
  intro w
  have hH := equidistributedGrowingPrimePool_mass_one_le (V w) (Q w) w (hQ w)
  have hp := equidistributedGrowingPrimePool_mass_pos (V w) (Q w) w (hQ w)
  rw [abs_of_pos (div_pos zero_lt_one (mul_pos (hLower w) hp))]
  simp only [pow_zero, mul_one]
  exact one_div_le_one_div_of_le (hLower w) (by nlinarith [hLower w])

theorem equidistributedGrowingPrimePool_atom_rapid {V Q p : ℕ → ℕ}
    (hQ : ∀ w, 1 ≤ Q w) (hV : ∀ᶠ w in atTop, 1 ≤ V w) :
    RapidlySmall atTop (fun w => (V w : ℝ)) (fun w =>
      primePoolMass (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).lower
        (equidistributedGrowingPrimePool (V w) (Q w) w (hQ w)).upper (p w)) := by
  apply (equidistributedGrowingPrimePool_atom_cap_rapid hQ hV).of_abs_le
  apply Eventually.of_forall
  intro w
  rw [abs_of_nonneg (primePoolMass_nonneg _ _ _)]
  exact (primePool_max_atom (Nat.pow_pos (by decide : 0 < 2))
    (equidistributedGrowingPrimePool_mass_pos (V w) (Q w) w (hQ w)) (p w)).trans (le_abs_self _)

end Hindman168
