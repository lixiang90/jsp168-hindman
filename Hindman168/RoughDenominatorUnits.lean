import Hindman168.RationalResidueRows
import Hindman168.MasterPrimeSquarefreeLaw
import Hindman168.FiniteMasterSelection

/-!
# Smooth and actual prime-pool denominators are units

The smooth part is supported on primorial. A prime larger than V is
coprime to every positive divisor at most V. The master pool growth
places all actually supported slots above V eventually, uniformly over
varying choices from a fixed finite set of gaps.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

theorem smooth_denominator_coprime {W a k : ℕ} (e : ℕ) (ha : a ∣ W ^ e)
    (hk : W.Coprime k) : a.Coprime k :=
  Nat.Coprime.of_dvd_left ha (hk.pow_left e)

theorem fixed_denominator_coprime_rough {a w k : ℕ} (ha : a ≠ 0) (hw : a ≤ w)
    (hk : (primorial w).Coprime k) : a.Coprime k :=
  smooth_denominator_coprime w (fixed_integer_dvd_primorial_power ha hw) hk

theorem fixed_denominator_eventually_coprime_rough (a : ℕ) (ha : a ≠ 0) :
    ∀ᶠ w in atTop, ∀ k, (primorial w).Coprime k → a.Coprime k :=
  (eventually_ge_atTop a).mono (fun _ hw _ hk => fixed_denominator_coprime_rough ha hw hk)

theorem large_prime_coprime_bounded {p k V : ℕ} (hp : p.Prime) (hV : V < p)
    (hk : 0 < k) (hcap : k ≤ V) : p.Coprime k := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have hle := (Nat.le_of_dvd hk hd).trans hcap
  omega

theorem smooth_pool_denominator_coprime {r : ℕ} {W V k a : ℕ} (e : ℕ)
    (x t : Fin r → ℕ) (hx : ∀ j, (x j).Prime ∧ V < x j)
    (hk : 0 < k) (hcap : k ≤ V) (hW : W.Coprime k)
    (ha : a ∣ W ^ e * ∏ j, x j ^ t j) : a.Coprime k := by
  apply Nat.Coprime.of_dvd_left ha
  apply Nat.coprime_mul_iff_left.mpr
  refine ⟨hW.pow_left e, Nat.Coprime.prod_left (fun j _ => ?_)⟩
  exact (large_prime_coprime_bounded (hx j).1 (hx j).2 hk hcap).pow_left (t j)

theorem masterPrimeSlotsMass_support {r : ℕ} (F : MasterParameterFamily) (w : ℕ)
    (gap : Fin r → ℕ) {x : Fin r → ℕ} (hx : x ∈ (masterPrimeSlotsMass F w gap).support)
    (j : Fin r) : (F.pool w (gap j)).lower ≤ x j ∧
      x j < (F.pool w (gap j)).upper ∧ (x j).Prime := by
  have hne := Finsupp.mem_support_iff.mp hx
  change piMass (fun j => primePoolMass (F.pool w (gap j)).lower (F.pool w (gap j)).upper) x ≠ 0 at hne
  rw [piMass_apply] at hne
  exact primePool_mem.mp (primePoolMass_support _ _ (Finsupp.mem_support_iff.mpr
    (Finset.prod_ne_zero_iff.mp hne j (Finset.mem_univ j))))

theorem MasterParameterConditions.prime_slots_eventually_gt_budget {n N r L : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap : ℕ → Fin r → Fin L) (V : ℕ → ℕ)
    (hbudget : ∀ᶠ w in atTop, ∀ j, V w ≤ F.auxiliary w (gap w j)) :
    ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => gap w j)).support,
      ∀ j, (x j).Prime ∧ V w < x j := by
  have hlarge : ∀ᶠ w in atTop, ∀ l : Fin L,
      F.auxiliary w l.val < (F.pool w l.val).lower := by
    apply eventually_all.mpr
    intro l
    filter_upwards [(hF.pool_lower_growth l.val).eventually_bound
      (Eventually.of_forall (fun _ => Nat.cast_nonneg _))
      (Eventually.of_forall (fun _ => Nat.cast_nonneg _)) 1 (by norm_num : (0 : ℝ) < 2)] with w hw
    simp only [pow_one] at hw
    have haux : (0 : ℝ) < F.auxiliary w l.val := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (F.auxiliary_ge_two w l.val))
    have hlt : (F.auxiliary w l.val : ℝ) < (F.pool w l.val).lower := by linarith
    exact_mod_cast hlt
  filter_upwards [hlarge, hbudget] with w hw hb
  intro x hx j
  have hs := masterPrimeSlotsMass_support F w (fun j => gap w j) hx j
  exact ⟨hs.2.2, lt_of_le_of_lt (hb j) ((hw (gap w j)).trans_le hs.1)⟩

end Hindman168
