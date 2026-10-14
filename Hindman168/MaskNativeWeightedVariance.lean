import Hindman168.MaskNativeMixedMoments
import Hindman168.FiniteCenteredWeightedReplacement

/-! The actual original paper weighted variance E B(H-2^t)^2 tends
to zero. This follows from the three native joint moments, rather than
from a cancellation of unrelated array expectations. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskRootOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

local notation "d" => rootMomentDimension m gap t

noncomputable def retainedMeanConstant (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) : ℝ :=
  (((2 ^ (rootMomentDimension m gap t * 2 ^ (rootMomentDimension m gap t - 1)) : ℕ) : ℝ))

noncomputable def nativeVariance (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (w : ℕ) : ℝ :=
  expectation (nativeJointMass gap C t J w) (fun p => nativeB gap C t a label w p *
    (nativeH gap C t a label w p - retainedMeanConstant m gap t) ^ 2)

theorem nativeVariance_eq (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) (w : ℕ) :
    nativeVariance gap a C t J label w = nativeSecondMoment gap C t J a label w -
      2 * retainedMeanConstant m gap t * nativeFirstMoment gap C t J a label w +
        retainedMeanConstant m gap t ^ 2 * targetMajorantAverage gap a C t J label w := by
  unfold nativeVariance
  rw [expectation_centered_weighted_square, nativeB_average_eq]
  rfl

include ha hC hJ hgap in
theorem nativeVariance_tendsto_zero
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    Tendsto (nativeVariance gap a C t J label) atTop (𝓝 0) := by
  have h₀ := targetMajorantAverage_tendsto gap a ha C hC t J hJ hgap htail label
  have h₁ := nativeFirstMoment_tendsto gap a ha C hC t J hJ hgap htail label
  have h₂ := nativeSecondMoment_tendsto gap a ha C hC t J hJ hgap htail label
  have ht := (h₂.sub (h₁.const_mul (2 * retainedMeanConstant m gap t))).add
    (h₀.const_mul (retainedMeanConstant m gap t ^ 2))
  have he : (((2 ^ (2 ^ d + 2 * (d * 2 ^ (d - 1))) : ℕ) : ℝ)) -
      2 * retainedMeanConstant m gap t * (((2 ^ (2 ^ d + d * 2 ^ (d - 1)) : ℕ) : ℝ)) +
      retainedMeanConstant m gap t ^ 2 * (((2 ^ (2 ^ d) : ℕ) : ℝ)) = 0 := by
    unfold retainedMeanConstant
    simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, pow_add]
    rw [show 2 * (d * 2 ^ (d - 1)) = (d * 2 ^ (d - 1)) * 2 by omega, pow_mul]
    ring
  rw [he] at ht
  exact ht.congr (fun w => (nativeVariance_eq gap a C t J label w).symm)

end Hindman168.MaskRootOriginalSampling
