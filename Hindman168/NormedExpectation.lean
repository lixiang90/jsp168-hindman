import Hindman168.FiniteMass
import Hindman168.PowerGrowth
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Polynomially bounded normed-space test functions

Finite real masses act on real normed spaces by scalar multiplication.
This includes complex-valued tests. The L1 transfer retains the actual
unnormalized comparison mass and has no probability hypothesis.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators

noncomputable def normedExpectation {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Mass α) (f : α → E) : E := μ.sum (fun x a => a • f x)

theorem normedExpectation_difference_bound {α E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ ν : Mass α) (f : α → E) (B : ℝ) (hf : ∀ x, ‖f x‖ ≤ B) :
    ‖normedExpectation μ f - normedExpectation ν f‖ ≤ B * distance μ ν := by
  have he : normedExpectation (μ - ν) f = normedExpectation μ f - normedExpectation ν f :=
    Finsupp.sum_sub_index (fun _ a b => sub_smul a b _)
  rw [← he]
  unfold normedExpectation distance variation Finsupp.sum
  calc
    _ ≤ ∑ x ∈ (μ - ν).support, ‖(μ - ν) x • f x‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ (μ - ν).support, |(μ - ν) x| * B := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)
    _ = B * ∑ x ∈ (μ - ν).support, |(μ - ν) x| := by rw [← Finset.sum_mul, mul_comm]

end Hindman168.FiniteMass

namespace Hindman168

open Filter Asymptotics
open scoped Topology

theorem normed_expectation_transfer_rapid {α β E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {l : Filter α}
    {V : α → ℕ} {μ ν : α → FiniteMass.Mass β} {e : α → ℝ}
    (hV : ∀ᶠ w in l, 0 < V w)
    (he : RapidlySmall l (fun w => (V w : ℝ)) e)
    (hd : ∀ᶠ w in l, FiniteMass.distance (μ w) (ν w) ≤ e w)
    (B : ℕ) (f : α → β → E)
    (hf : ∀ᶠ w in l, ∀ b, ‖f w b‖ ≤ (V w : ℝ) ^ B) :
    RapidlySmall l (fun w => (V w : ℝ))
      (fun w => ‖FiniteMass.normedExpectation (μ w) (f w) -
        FiniteMass.normedExpectation (ν w) (f w)‖) := by
  apply (he.mul_power (hV.mono (fun _ hw => by exact_mod_cast hw)) B).of_abs_le
  filter_upwards [hd, hf] with w hdw hfw
  rw [abs_of_nonneg (norm_nonneg _)]
  exact (FiniteMass.normedExpectation_difference_bound (μ w) (ν w) (f w)
    ((V w : ℝ) ^ B) hfw).trans
      ((mul_le_mul_of_nonneg_left hdw (pow_nonneg (Nat.cast_nonneg _) B)).trans (le_abs_self _))

theorem normed_expectation_transfer_isLittleO {α β E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {l : Filter α}
    {V : α → ℕ} {μ ν : α → FiniteMass.Mass β} {e : α → ℝ}
    (hV : ∀ᶠ w in l, 0 < V w)
    (he : RapidlySmall l (fun w => (V w : ℝ)) e)
    (hd : ∀ᶠ w in l, FiniteMass.distance (μ w) (ν w) ≤ e w)
    (B : ℕ) (f : α → β → E)
    (hf : ∀ᶠ w in l, ∀ b, ‖f w b‖ ≤ (V w : ℝ) ^ B) (C : ℝ) :
    (fun w => FiniteMass.normedExpectation (μ w) (f w) -
      FiniteMass.normedExpectation (ν w) (f w)) =o[l] (fun w => (V w : ℝ) ^ (-C)) := by
  apply isLittleO_norm_left.mp
  exact (normed_expectation_transfer_rapid hV he hd B f hf).rpow_scale
    (hV.mono (fun w hw => by exact_mod_cast (by omega : 1 ≤ V w))) C

end Hindman168
