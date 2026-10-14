import Hindman168.MaskRootOriginalLaw
import Hindman168.RootSmoothedMomentIndices

/-! Three concrete enlarged-array moments under the unchanged normalized
original good-prime law. Their exact exponents are derived from canonical
copy counts. Native B, BH and BH^2 identifications are a separate step. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskRootOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

local notation "S" => maskRootOriginalSampling m gap a ha C hC t J hJ hgap
noncomputable abbrev rootMomentDimension (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) : ℕ :=
  Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)

local notation "d" => rootMomentDimension m gap t

noncomputable def targetArrayMoment
    (label : ℕ → (S).BaseRow → Fin (m + 1)) : ℕ → ℝ :=
  (S).fullMajorant label (rootMomentTarget d)

noncomputable def firstArrayMoment
    (label : ℕ → (S).BaseRow → Fin (m + 1)) : ℕ → ℝ :=
  (S).fullMajorant label (rootMomentFirst d)

noncomputable def secondArrayMoment
    (label : ℕ → (S).BaseRow → Fin (m + 1)) : ℕ → ℝ :=
  (S).fullMajorant label (rootMomentSecond d)

theorem targetArrayMoment_tendsto
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → (S).BaseRow → Fin (m + 1)) :
    Tendsto (targetArrayMoment gap a ha C hC t J hJ hgap label) atTop (𝓝 (((2 ^ (2 ^ d) : ℕ) : ℝ))) := by
  have ht := fullMajorant_tendsto gap a ha C hC t J hJ hgap htail label (rootMomentTarget d)
  have hc := congrArg (fun q : ℕ =>
    Tendsto ((S).fullMajorant label (rootMomentTarget d)) atTop (𝓝 (((2 ^ q : ℕ) : ℝ))))
      (rootMomentTarget_card d)
  exact hc.mp ht

theorem firstArrayMoment_tendsto
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → (S).BaseRow → Fin (m + 1)) :
    Tendsto (firstArrayMoment gap a ha C hC t J hJ hgap label) atTop
      (𝓝 (((2 ^ (2 ^ d + d * 2 ^ (d - 1)) : ℕ) : ℝ))) := by
  have ht := fullMajorant_tendsto gap a ha C hC t J hJ hgap htail label (rootMomentFirst d)
  have hc := congrArg (fun q : ℕ =>
    Tendsto ((S).fullMajorant label (rootMomentFirst d)) atTop (𝓝 (((2 ^ q : ℕ) : ℝ))))
      (rootMomentFirst_card d)
  exact hc.mp ht

theorem secondArrayMoment_tendsto
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → (S).BaseRow → Fin (m + 1)) :
    Tendsto (secondArrayMoment gap a ha C hC t J hJ hgap label) atTop
      (𝓝 (((2 ^ (2 ^ d + 2 * (d * 2 ^ (d - 1))) : ℕ) : ℝ))) := by
  have ht := fullMajorant_tendsto gap a ha C hC t J hJ hgap htail label (rootMomentSecond d)
  have hc := congrArg (fun q : ℕ =>
    Tendsto ((S).fullMajorant label (rootMomentSecond d)) atTop (𝓝 (((2 ^ q : ℕ) : ℝ))))
      (rootMomentSecond_card d)
  exact hc.mp ht

theorem array_moment_centering_tendsto_zero
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → (S).BaseRow → Fin (m + 1)) :
    Tendsto (fun w => secondArrayMoment gap a ha C hC t J hJ hgap label w -
      2 * (((2 ^ (d * 2 ^ (d - 1)) : ℕ) : ℝ)) * firstArrayMoment gap a ha C hC t J hJ hgap label w +
      (((2 ^ (d * 2 ^ (d - 1)) : ℕ) : ℝ)) ^ 2 * targetArrayMoment gap a ha C hC t J hJ hgap label w)
      atTop (𝓝 0) := by
  have h₀ := targetArrayMoment_tendsto gap a ha C hC t J hJ hgap htail label
  have h₁ := firstArrayMoment_tendsto gap a ha C hC t J hJ hgap htail label
  have h₂ := secondArrayMoment_tendsto gap a ha C hC t J hJ hgap htail label
  have ht := (h₂.sub (h₁.const_mul (2 * (((2 ^ (d * 2 ^ (d - 1)) : ℕ) : ℝ))))).add
    (h₀.const_mul ((((2 ^ (d * 2 ^ (d - 1)) : ℕ) : ℝ)) ^ 2))
  have he : (((2 ^ (2 ^ d + 2 * (d * 2 ^ (d - 1))) : ℕ) : ℝ)) -
      2 * (((2 ^ (d * 2 ^ (d - 1)) : ℕ) : ℝ)) * (((2 ^ (2 ^ d + d * 2 ^ (d - 1)) : ℕ) : ℝ)) +
      (((2 ^ (d * 2 ^ (d - 1)) : ℕ) : ℝ)) ^ 2 * (((2 ^ (2 ^ d) : ℕ) : ℝ)) = 0 := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, pow_add]
    rw [show 2 * (d * 2 ^ (d - 1)) = (d * 2 ^ (d - 1)) * 2 by omega, pow_mul]
    ring
  rw [he] at ht
  exact ht

end Hindman168.MaskRootOriginalSampling
