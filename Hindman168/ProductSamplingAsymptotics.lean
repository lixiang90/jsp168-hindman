import Hindman168.IntegerProductLaw
import Hindman168.SamplingAsymptotics
import Hindman168.FiniteTensor

/-!
# Inverse-power error rates for the actual block-product law

The finite tail law is conditioned upon, retaining the unnormalized
divisor-mask comparison. The growth assumption is imposed on log X.
Validity of the tail cutoffs is still an explicit hypothesis here; the
full prime and master parameter construction is a separate step.
-/

namespace Hindman168

open Filter Asymptotics
open scoped Topology

theorem product_law_rapid {α : Type*} {l : Filter α}
    {X W K V : α → ℕ} {ρ : α → FiniteMass.Mass ℕ}
    (hD : PowerDominates l (fun w => Real.log (X w))
      (fun w => (samplingSize (W w) (K w) 0 (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w) (hK : ∀ᶠ w in l, 1 ≤ K w)
    (hW : ∀ᶠ w in l, 0 < W w)
    (hρ : ∀ᶠ w in l, ∀ k, 0 ≤ ρ w k)
    (htρ : ∀ᶠ w in l, FiniteMass.total (ρ w) = 1)
    (hs : ∀ᶠ w in l, ∀ k ∈ (ρ w).support,
      0 < k ∧ k ≤ K w ∧ (W w).Coprime k) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w =>
      FiniteMass.distance (productMass (ρ w) (X w) (W w))
        (productComparisonMass (ρ w) (X w) (W w))) := by
  apply (dilationError_rapid hD hK hV).of_abs_le
  filter_upwards [sampling_eventually_geometry (powerDominates_log_to_cutoff hD),
    hW, hρ, htρ, hs] with w hw hWw hρw htρw hsw
  have hx : 2 ≤ X w := by omega
  have hl := sampling_denominator_pos hw.1 hw.2.1
  rw [abs_of_nonneg (FiniteMass.distance_nonneg _ _)]
  exact (product_law_error hρw htρw hx hWw hw.2.2 hsw hl).trans (le_abs_self _)

theorem product_comparison_mass_rapid {α : Type*} {l : Filter α}
    {X W K V : α → ℕ} {ρ : α → FiniteMass.Mass ℕ}
    (hD : PowerDominates l (fun w => Real.log (X w))
      (fun w => (samplingSize (W w) (K w) 0 (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w) (hW : ∀ᶠ w in l, 0 < W w)
    (hρ : ∀ᶠ w in l, ∀ k, 0 ≤ ρ w k)
    (htρ : ∀ᶠ w in l, FiniteMass.total (ρ w) = 1)
    (hs : ∀ᶠ w in l, ∀ k ∈ (ρ w).support,
      0 < k ∧ k ≤ K w ∧ (W w).Coprime k) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w =>
      FiniteMass.total (productComparisonMass (ρ w) (X w) (W w)) - 1) := by
  apply (residueError_rapid (powerDominates_log_to_cutoff hD) hV).of_abs_le
  filter_upwards [sampling_eventually_geometry (powerDominates_log_to_cutoff hD),
    hW, hρ, htρ, hs] with w hw hWw hρw htρw hsw
  have hx : 2 ≤ X w := by omega
  have hl := sampling_denominator_pos hw.1 hw.2.1
  exact (product_comparison_mass_error hρw htρw hx hWw hsw hl).trans (le_abs_self _)

theorem tailBound_pos (Xs : List ℕ) (W : ℕ) (hv : ValidCutoffs Xs W) :
    0 < tailBound Xs := by
  induction Xs with
  | nil => simp [tailBound]
  | cons X Xs ih =>
    have hh := validCutoffs_head hv
    have ht := ih (validCutoffs_tail hv)
    simpa only [tailBound, List.map_cons, List.prod_cons] using
      Nat.mul_pos (pow_pos (by omega : 0 < X) 2) ht

theorem block_product_law_rapid {α : Type*} {l : Filter α}
    {X W V : α → ℕ} {Xs : α → List ℕ}
    (hD : PowerDominates l (fun w => Real.log (X w))
      (fun w => (samplingSize (W w) (tailBound (Xs w)) 0 (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w) (hW : ∀ᶠ w in l, 0 < W w)
    (hv : ∀ᶠ w in l, ValidCutoffs (Xs w) (W w)) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w =>
      FiniteMass.distance (productMass (tailMass (W w) (Xs w)) (X w) (W w))
        (productComparisonMass (tailMass (W w) (Xs w)) (X w) (W w))) := by
  apply product_law_rapid hD hV (hv.mono (fun w hw => tailBound_pos (Xs w) (W w) hw)) hW
  · filter_upwards [hW, hv] with w hWw hvw
    exact tailMass_nonneg hWw (Xs w) hvw
  · filter_upwards [hW, hv] with w hWw hvw
    exact tailMass_total hWw (Xs w) hvw
  · exact hv.mono (fun w hw => tailMass_support (Xs w) hw)

theorem block_product_comparison_mass_rapid {α : Type*} {l : Filter α}
    {X W V : α → ℕ} {Xs : α → List ℕ}
    (hD : PowerDominates l (fun w => Real.log (X w))
      (fun w => (samplingSize (W w) (tailBound (Xs w)) 0 (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w) (hW : ∀ᶠ w in l, 0 < W w)
    (hv : ∀ᶠ w in l, ValidCutoffs (Xs w) (W w)) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w =>
      FiniteMass.total (productComparisonMass (tailMass (W w) (Xs w)) (X w) (W w)) - 1) := by
  apply product_comparison_mass_rapid hD hV hW
  · filter_upwards [hW, hv] with w hWw hvw
    exact tailMass_nonneg hWw (Xs w) hvw
  · filter_upwards [hW, hv] with w hWw hvw
    exact tailMass_total hWw (Xs w) hvw
  · exact hv.mono (fun w hw => tailMass_support (Xs w) hw)

theorem integer_block_product_law_rapid {α : Type*} {l : Filter α}
    {X W V : α → ℕ} {Xs : α → List ℕ}
    (hD : PowerDominates l (fun w => Real.log (X w))
      (fun w => (samplingSize (W w) (tailBound (Xs w)) 0 (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w) (hW : ∀ᶠ w in l, 0 < W w)
    (hv : ∀ᶠ w in l, ValidCutoffs (Xs w) (W w)) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w =>
      FiniteMass.distance (integerProductMass (tailMass (W w) (Xs w)) (X w) (W w))
        (integerProductComparisonMass (tailMass (W w) (Xs w)) (X w) (W w))) := by
  simpa only [integerProductMass, integerProductComparisonMass,
    FiniteMass.distance_push_injective (f := fun n : ℕ => (n : ℤ)) Int.ofNat_injective] using
    block_product_law_rapid hD hV hW hv

end Hindman168
