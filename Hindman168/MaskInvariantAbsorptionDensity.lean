import Hindman168.MaskInvariantProductMerge

/-! The density outside the two branch tests is also dilated when pq
is absorbed in the selected harmonic coordinate. Its invariant rows are
preserved by that dilation, identifying the actual surviving Omega. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

variable {m : ℕ}

theorem maskSingleTag_eq_balanced_projection (u v j : Fin (m + 1)) :
    maskSingleTag u j = (if maskBalancedTag u v j = 1 then 1 else 0 : Fin 3) := by
  by_cases hu : j = u
  · simp [maskSingleTag, maskBalancedTag, hu]
  · by_cases hv : j = v <;> simp [maskSingleTag, maskBalancedTag, hu, hv]

theorem maskRowInvariant_balanced_single {R : Type*} [Zero R]
    (A : Fin (m + 1) → R) (u v : Fin (m + 1))
    (hi : maskRowInvariant A (maskBalancedTag u v)) :
    maskRowInvariant A (maskSingleTag u) := by
  intro j k hj hk
  rw [maskSingleTag_eq_balanced_projection u v j,
    maskSingleTag_eq_balanced_projection u v k, hi j k hj hk]

namespace MaskColumnPlan

variable {S U : Finset (Fin (m + 1))}

noncomputable def absorptionCoordinates (P : MaskColumnPlan S U) (p q : ℕ)
    (z : Fin (m + 1) → ℤ) : Fin (m + 1) → ℤ :=
  match P with
  | .outside _ _ _ => z
  | .balanced u _ _ _ _ _ _ => Function.update z u (((p*q : ℕ) : ℤ) * z u)

theorem invariantIntegerMask_absorption {n r : ℕ} (P : MaskColumnPlan S U)
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r)
    (hi : maskRowInvariant (F.row i) P.tag) (ρ : Mass ℕ) (p q : ℕ)
    (hp : ∀ d ∈ ρ.support, p.Coprime d) (hq : ∀ d ∈ ρ.support, q.Coprime d)
    (z : Fin (m + 1) → ℤ) :
    integerDivisorMask ρ (F.normalizedIntegerLinearForm x c i (P.absorptionCoordinates p q z)) =
      integerDivisorMask ρ (F.normalizedIntegerLinearForm x c i z) := by
  cases P with
  | outside u hu hU => rfl
  | balanced u v hu hv huU hvU hne =>
    exact F.invariantIntegerMask_single x c i u
      (maskRowInvariant_balanced_single (F.row i) u v hi) ρ (p*q)
      (fun d hd => (hp d hd).mul_left (hq d hd)) z

end MaskColumnPlan

variable {N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

include hC htail in
theorem maskStageInvariantWeight_absorptionDilation :
    ∀ᶠ w in atTop, ∀ k U i, i ∈ maskStageInvariantRows S hS k U →
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ q ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper, ∀ x z,
      monomialRowWeight gap a C (maskPrefixRowStage S hS k).rows
        (fun _ i => (maskPrefixRowStage S hS k).rows.normalizationAnchor i) (fun _ => id) w i x
        ((chosenMaskColumnPlan S U hS).absorptionCoordinates p q z) =
      monomialRowWeight gap a C (maskPrefixRowStage S hS k).rows
        (fun _ i => (maskPrefixRowStage S hS k).rows.normalizationAnchor i) (fun _ => id) w i x z := by
  filter_upwards [maskTail_fresh_prime_units gap C hC htail] with w hu
  intro k U i hi p hp q hq x z
  exact (chosenMaskColumnPlan S U hS).invariantIntegerMask_absorption
    (maskPrefixRowStage S hS k).rows x _ i (Finset.mem_filter.mp hi).2 _ p q
    (hu _ p hp) (hu _ q hq) z

include hC htail in
theorem maskStageInvariantDensity_absorptionDilation :
    ∀ᶠ w in atTop, ∀ k U,
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ q ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper, ∀ x z,
      maskStageDensity S hS gap a C k U w
        (x, (chosenMaskColumnPlan S U hS).absorptionCoordinates p q z) =
      maskStageDensity S hS gap a C k U w (x, z) := by
  filter_upwards [maskStageInvariantWeight_absorptionDilation S hS gap a C hC htail] with w hw
  intro k U p hp q hq x z
  unfold maskStageDensity
  apply Finset.prod_congr rfl
  intro i hi
  rw [hw k U i hi p hp q hq x z]

include hC htail in
theorem maskStageInvariantProducts_eventually_absorptionMerge :
    ∀ᶠ w in atTop, ∀ k U,
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ q ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ f g : Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ, ∀ x z,
      maskStageDensity S hS gap a C k U w
        (x, (chosenMaskColumnPlan S U hS).absorptionCoordinates p q z) *
        maskStageInvariantRatioProduct S hS gap a C k U w f x
          ((chosenMaskColumnPlan S U hS).absorbedCoordinates p q z) *
        maskStageInvariantRatioProduct S hS gap a C k U w g x
          ((chosenMaskColumnPlan S U hS).absorbedCoordinates q p z) =
      maskStageInvariantMergedProduct S hS gap a C k U w p q f g x z := by
  filter_upwards [maskStageInvariantDensity_absorptionDilation S hS gap a C hC htail,
    maskStageInvariantProducts_eventually_merge S hS gap a C hC htail] with w hd hm
  intro k U p hp q hq f g x z
  rw [hd k U p hp q hq x z]
  exact hm k U p hp q hq f g x z

end Hindman168
