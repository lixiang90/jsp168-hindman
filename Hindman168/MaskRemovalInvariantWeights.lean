import Hindman168.MaskInvariantCoordinateForms

/-! The invariant divisor masks and the single invariant-row density
are preserved under actual mask substitutions and both absorbed branches.
The old prime tuple is fixed throughout these pointwise identities. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

variable {n r m : ℕ}

theorem PolynomialRowFamily.invariantIntegerMask_single
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r)
    (u : Fin (m + 1)) (hi : maskRowInvariant (F.row i) (maskSingleTag u))
    (ρ : Mass ℕ) (p : ℕ) (hp : ∀ d ∈ ρ.support, p.Coprime d)
    (z : Fin (m + 1) → ℤ) :
    integerDivisorMask ρ (F.normalizedIntegerLinearForm x c i (Function.update z u ((p : ℤ) * z u))) =
      integerDivisorMask ρ (F.normalizedIntegerLinearForm x c i z) := by
  rw [F.invariantIntegerForm_single x c i u hi p z]
  apply integerDivisorMask_unit_scaled
  intro d hd
  unfold maskSingleScalar
  split_ifs
  · exact hp d hd
  · exact Nat.coprime_one_left d

theorem PolynomialRowFamily.invariantIntegerMask_balanced
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r)
    (u v : Fin (m + 1)) (hne : u ≠ v)
    (hi : maskRowInvariant (F.row i) (maskBalancedTag u v))
    (ρ : Mass ℕ) (p : ℕ) (hp : ∀ d ∈ ρ.support, p.Coprime d)
    (z : Fin (m + 1) → ℤ) (hd : (p : ℤ) ∣ z u) :
    integerDivisorMask ρ (F.normalizedIntegerLinearForm x c i (maskBalancedCoordinates u v p z)) =
      integerDivisorMask ρ (F.normalizedIntegerLinearForm x c i z) := by
  calc
    _ = integerDivisorMask ρ ((p : ℤ) *
        F.normalizedIntegerLinearForm x c i (maskBalancedCoordinates u v p z)) :=
      (integerDivisorMask_unit_scaled ρ p _ hp).symm
    _ = integerDivisorMask ρ ((maskBalancedClearScalar p (maskBalancedTag u v (F.normalizationAnchor i)) : ℤ) *
        F.normalizedIntegerLinearForm x c i z) := by
      rw [F.invariantIntegerForm_balanced_cleared x c i u v hne hi p z hd]
    _ = _ := by
      apply integerDivisorMask_unit_scaled
      intro d hρ
      unfold maskBalancedClearScalar
      split_ifs
      · exact Nat.coprime_one_left d
      · exact (hp d hρ).pow_left 2
      · exact hp d hρ

theorem PolynomialRowFamily.invariantIntegerMask_absorbed
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r)
    (u v : Fin (m + 1)) (hne : u ≠ v)
    (hi : maskRowInvariant (F.row i) (maskBalancedTag u v))
    (ρ : Mass ℕ) (p q : ℕ)
    (hp : ∀ d ∈ ρ.support, p.Coprime d) (hq : ∀ d ∈ ρ.support, q.Coprime d)
    (z : Fin (m + 1) → ℤ) :
    integerDivisorMask ρ (F.normalizedIntegerLinearForm x c i (maskAbsorbedCoordinates u v p q z)) =
      integerDivisorMask ρ (F.normalizedIntegerLinearForm x c i z) := by
  rw [F.invariantIntegerForm_absorbed x c i u v hne hi p q z]
  apply integerDivisorMask_unit_scaled
  intro d hd
  unfold maskAbsorbedScalar
  split_ifs
  · exact hq d hd
  · exact hp d hd
  · exact Nat.coprime_one_left d

namespace MaskColumnPlan

variable {S U : Finset (Fin (m + 1))}

noncomputable def coordinates (P : MaskColumnPlan S U) (p : ℕ) (z : Fin (m + 1) → ℤ) :
    Fin (m + 1) → ℤ :=
  match P with
  | .outside u _ _ => Function.update z u ((p : ℤ) * z u)
  | .balanced u v _ _ _ _ _ => maskBalancedCoordinates u v p z

def admissible (P : MaskColumnPlan S U) (p : ℕ) (z : Fin (m + 1) → ℤ) : Prop :=
  match P with
  | .outside _ _ _ => True
  | .balanced u _ _ _ _ _ _ => (p : ℤ) ∣ z u

noncomputable def absorbedCoordinates (P : MaskColumnPlan S U) (p q : ℕ)
    (z : Fin (m + 1) → ℤ) : Fin (m + 1) → ℤ :=
  match P with
  | .outside u _ _ => Function.update z u ((p : ℤ) * z u)
  | .balanced u v _ _ _ _ _ => maskAbsorbedCoordinates u v p q z

theorem invariantIntegerMask_preserved (P : MaskColumnPlan S U)
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r)
    (hi : maskRowInvariant (F.row i) P.tag) (ρ : Mass ℕ) (p : ℕ)
    (hp : ∀ d ∈ ρ.support, p.Coprime d) (z : Fin (m + 1) → ℤ) (hd : P.admissible p z) :
    integerDivisorMask ρ (F.normalizedIntegerLinearForm x c i (P.coordinates p z)) =
      integerDivisorMask ρ (F.normalizedIntegerLinearForm x c i z) := by
  cases P with
  | outside u hu hU => exact F.invariantIntegerMask_single x c i u hi ρ p hp z
  | balanced u v hu hv huU hvU hne =>
    exact F.invariantIntegerMask_balanced x c i u v hne hi ρ p hp z hd

theorem invariantIntegerMask_absorbed (P : MaskColumnPlan S U)
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r)
    (hi : maskRowInvariant (F.row i) P.tag) (ρ : Mass ℕ) (p q : ℕ)
    (hp : ∀ d ∈ ρ.support, p.Coprime d) (hq : ∀ d ∈ ρ.support, q.Coprime d)
    (z : Fin (m + 1) → ℤ) :
    integerDivisorMask ρ (F.normalizedIntegerLinearForm x c i (P.absorbedCoordinates p q z)) =
      integerDivisorMask ρ (F.normalizedIntegerLinearForm x c i z) := by
  cases P with
  | outside u hu hU => exact F.invariantIntegerMask_single x c i u hi ρ p hp z
  | balanced u v hu hv huU hvU hne =>
    exact F.invariantIntegerMask_absorbed x c i u v hne hi ρ p q hp hq z

end MaskColumnPlan

variable {N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

include hC htail in
theorem maskStageInvariantWeight_preserved :
    ∀ᶠ w in atTop, ∀ k U i, i ∈ maskStageInvariantRows S hS k U →
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper, ∀ x z,
      (chosenMaskColumnPlan S U hS).admissible p z →
      monomialRowWeight gap a C (maskPrefixRowStage S hS k).rows
        (fun _ i => (maskPrefixRowStage S hS k).rows.normalizationAnchor i) (fun _ => id) w i x
        ((chosenMaskColumnPlan S U hS).coordinates p z) =
      monomialRowWeight gap a C (maskPrefixRowStage S hS k).rows
        (fun _ i => (maskPrefixRowStage S hS k).rows.normalizationAnchor i) (fun _ => id) w i x z := by
  filter_upwards [maskTail_fresh_prime_units gap C hC htail] with w hu
  intro k U i hi p hp x z hd
  exact (chosenMaskColumnPlan S U hS).invariantIntegerMask_preserved
    (maskPrefixRowStage S hS k).rows x _ i (Finset.mem_filter.mp hi).2 _ p
    (hu _ p hp) z hd

include hC htail in
theorem maskStageInvariantWeight_absorbed :
    ∀ᶠ w in atTop, ∀ k U i, i ∈ maskStageInvariantRows S hS k U →
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ q ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper, ∀ x z,
      monomialRowWeight gap a C (maskPrefixRowStage S hS k).rows
        (fun _ i => (maskPrefixRowStage S hS k).rows.normalizationAnchor i) (fun _ => id) w i x
        ((chosenMaskColumnPlan S U hS).absorbedCoordinates p q z) =
      monomialRowWeight gap a C (maskPrefixRowStage S hS k).rows
        (fun _ i => (maskPrefixRowStage S hS k).rows.normalizationAnchor i) (fun _ => id) w i x z := by
  filter_upwards [maskTail_fresh_prime_units gap C hC htail] with w hu
  intro k U i hi p hp q hq x z
  exact (chosenMaskColumnPlan S U hS).invariantIntegerMask_absorbed
    (maskPrefixRowStage S hS k).rows x _ i (Finset.mem_filter.mp hi).2 _ p q
    (hu _ p hp) (hu _ q hq) z

include hC htail in
theorem maskStageInvariantDensity_preserved :
    ∀ᶠ w in atTop, ∀ k U,
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper, ∀ x z,
      (chosenMaskColumnPlan S U hS).admissible p z →
      maskStageDensity S hS gap a C k U w (x, (chosenMaskColumnPlan S U hS).coordinates p z) =
        maskStageDensity S hS gap a C k U w (x, z) := by
  filter_upwards [maskStageInvariantWeight_preserved S hS gap a C hC htail] with w hw
  intro k U p hp x z hd
  unfold maskStageDensity
  apply Finset.prod_congr rfl
  intro i hi
  rw [hw k U i hi p hp x z hd]

include hC htail in
theorem maskStageInvariantDensity_absorbed :
    ∀ᶠ w in atTop, ∀ k U,
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ q ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper, ∀ x z,
      maskStageDensity S hS gap a C k U w (x, (chosenMaskColumnPlan S U hS).absorbedCoordinates p q z) =
        maskStageDensity S hS gap a C k U w (x, z) := by
  filter_upwards [maskStageInvariantWeight_absorbed S hS gap a C hC htail] with w hw
  intro k U p hp q hq x z
  unfold maskStageDensity
  apply Finset.prod_congr rfl
  intro i hi
  rw [hw k U i hi p hp q hq x z]

end Hindman168
