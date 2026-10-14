import Hindman168.MasterSquareRootGapLengths
import Hindman168.MasterCyclicQuotients

namespace Hindman168
open Filter
open scoped Topology

theorem MasterParameterConditions.capped_short_lengths_eventually
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
    (gap : ℕ → Fin N) (J k B : ℕ) (hJ : 0 < J) :
    ∀ᶠ w in atTop, ∀ P : ℕ, 0 < P →
      J * P ≤ ((F.pool w (gap w).val).upper + F.auxiliary w (gap w).val) ^ k →
      B ≤ F.gap w (gap w).val / (J * P) := by
  have hg := PowerDominates.finite_choice (fun i : Fin N => hF.gap_growth i.val) gap
  filter_upwards [hg.eventually_bound (A := (B : ℝ) + 1)
    (Eventually.of_forall (fun _ => Nat.cast_nonneg _))
    (Eventually.of_forall (fun _ => by positivity)) k (by positivity)] with w hw
  intro P hP hcap
  have hR : (B + 1) *
      ((F.pool w (gap w).val).upper + F.auxiliary w (gap w).val) ^ k ≤ F.gap w (gap w).val := by
    exact_mod_cast hw
  have hb : B * (J * P) ≤ F.gap w (gap w).val :=
    (Nat.mul_le_mul (Nat.le_succ B) hcap).trans hR
  exact (Nat.le_div_iff_mul_le (Nat.mul_pos hJ hP)).mpr hb

end Hindman168
