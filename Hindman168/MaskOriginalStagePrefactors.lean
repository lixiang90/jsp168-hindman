import Hindman168.MaskCopiedOriginalSampling

/-! Original pivot laws, concrete common quotient intervals and the raw
stage-prefactor bound. The only ordering inputs are the actual chain tails
before the gap and the gap before every pivot. No moment or error limit is
assumed in this application. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def maskOriginalBaseMass (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (C : ℕ → Chain (m + 1)) (w : ℕ) : Mass (Fin (m + 1) → ℤ) :=
  piMass (fun col => integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))

namespace MaskOriginalSampling

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

local notation "S" => maskOriginalSampling m gap a ha C hC t J hJ hgap

theorem originalColumnMass_eq (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) (col : Fin (m + 1)) :
    (S).originalColumnMass w x col =
      integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w) := by
  have hj : (S).columnIndex (.inl col) ∈ (S).harmonic := maskOriginalHarmonic_inl m gap t col
  unfold MaskCopiedSampling.originalColumnMass
  rw [if_pos hj]
  change integerMass ((maskGeneratedMaster m gap).cutoff w
    (maskOriginalIndex m gap C hC t w (Fintype.equivFin
      (PolynomialRowFamily.AdditiveColumn (maskGeneratedRowDataFamily m gap t).target m) (.inl col))).val)
    (primorial w) = _
  rw [maskOriginalIndex_inl]

theorem directionMass_eq (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) (k : (S).Direction) :
    (S).directionMass w x k = uniformIntervalMass 0 (maskGeneratedShiftLength m gap t J w x) := rfl

theorem divisor_budget
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val) :
    ∀ᶠ w in atTop, ∀ col,
      tailBound (((S).chain w).tailCutoffs ((maskGeneratedMaster m (S).gap).cutoff w) col) ≤ (S).budget w := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [htail] with w hw
  intro col
  exact hF.chain_tail_budget_at_gap (C w) w col (gap w).val (hw col)

include hC in
theorem base_probability_eventually :
    ∀ᶠ w in atTop, (∀ z, 0 ≤ maskOriginalBaseMass m gap C w z) ∧
      total (maskOriginalBaseMass m gap C w) = 1 := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  have hz (col : Fin (m + 1)) :
      0 < harmonicNormalizer ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w) := by
    have hp : (C w).pivot col ∈ Finset.range N := hC w col (by simp [Chain.block])
    exact (hw _ hp).2.2
  exact ⟨piMass_nonneg _ (fun col z => integerMass_nonneg (hz col) z),
    piMass_total_one _ (fun col => integerMass_total (hz col))⟩

theorem stagePrefactor_eq_original
    (label : ℕ → (S).BaseRow → Fin (m + 1)) (w : ℕ) (K : Finset (S).Direction) (base : (S).BaseRow) :
    (S).stagePrefactor label w K base =
      conditionalFiniteAverage ((S).primeMass w) (fun _ => maskOriginalBaseMass m gap C w)
        (maskGeneratedCopiedPrimeGood m gap t w) (fun x z =>
          expectation (piMass (fun _k : (S).Direction => tensor
            (uniformIntervalMass 0 (maskGeneratedShiftLength m gap t J w x))
            (uniformIntervalMass 0 (maskGeneratedShiftLength m gap t J w x))))
            (fun v => ∏ u ∈ (S).stageIndices K base,
              (1 + (S).weight ((S).labels label) (S).rows w u x (additiveSampleCoordinates z v)))) := by
  have hb : (fun x => piMass ((S).originalColumnMass w x)) =
      (fun _ => maskOriginalBaseMass m gap C w) := by
    funext x
    apply congrArg piMass
    funext col
    exact originalColumnMass_eq gap a ha C hC t J hJ hgap w x col
  have hd : (fun x => piMass (fun k : (S).Direction => tensor
      ((S).directionMass w x k) ((S).directionMass w x k))) =
      (fun x => piMass (fun _k : (S).Direction => tensor
        (uniformIntervalMass 0 (maskGeneratedShiftLength m gap t J w x))
        (uniformIntervalMass 0 (maskGeneratedShiftLength m gap t J w x)))) := by
    funext x
    apply congrArg piMass
    funext k
    exact congrArg₂ tensor (directionMass_eq gap a ha C hC t J hJ hgap w x k)
      (directionMass_eq gap a ha C hC t J hJ hgap w x k)
  exact (congrArg (fun μ : (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → Mass (Fin (m + 1) → ℤ) => conditionalFiniteAverage ((S).primeMass w) μ
    (maskGeneratedCopiedPrimeGood m gap t w) (fun x z =>
      expectation (piMass (fun k => tensor ((S).directionMass w x k) ((S).directionMass w x k)))
        (fun v => ∏ u ∈ (S).stageIndices K base,
          (1 + (S).weight ((S).labels label) (S).rows w u x (additiveSampleCoordinates z v))))) hb).trans
    (congrArg (fun ν : (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → Mass ((S).Direction → ℤ × ℤ) => conditionalFiniteAverage ((S).primeMass w)
      (fun _ => maskOriginalBaseMass m gap C w) (maskGeneratedCopiedPrimeGood m gap t w)
      (fun x z => expectation (ν x) (fun v => ∏ u ∈ (S).stageIndices K base,
        (1 + (S).weight ((S).labels label) (S).rows w u x (additiveSampleCoordinates z v))))) hd)

theorem stagePrefactor_eventually_le
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → (S).BaseRow → Fin (m + 1)) (K : Finset (S).Direction) (base : (S).BaseRow) :
    ∀ᶠ w in atTop, (S).stagePrefactor label w K base ≤ maskCopiedMajorantBound m := by
  apply (S).stagePrefactor_eventually_le label
    ((divisor_budget gap a ha C hC t J hJ hgap htail).mono (fun w hw base => hw (label w base)))
  · intro k bit
    exact maskOriginalHarmonic_not_inr m gap t (k, bit)
  · intro w x k bit; rfl
  · intro w x k bit; rfl

end MaskOriginalSampling
end Hindman168
