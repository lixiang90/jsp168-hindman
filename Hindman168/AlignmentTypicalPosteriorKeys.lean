import Hindman168.AlignmentTypicalShortPosterior
import Hindman168.AlignmentDyadicExposureGeometry

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Topology Classical

noncomputable def alignmentShortPosteriorKeyGood {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n))
    (key : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ) × ℕ × ℕ) : Prop :=
  let a := ∏ j ∈ T, 2 ^ key.2.2.1 j
  let V := a * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)
  let Q := key.2.2.2.2 * V
  alignmentShortExposureDyadicGood F w T key ∧
    F.cutoff w i.val * (2 ^ T.card * a) ≤ Q ∧ Q + V ≤ F.cutoff w i.val ^ 2 * a

theorem alignmentShortPosteriorKeyGood_key {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ) :
    alignmentShortPosteriorKeyGood F w i T (alignmentShortExposureKey F w i T x) ↔
      alignmentTypicalShortPosterior F w i T x := by
  have hp : (∏ j ∈ T, (2 : ℕ) ^ (alignmentShortExposureKey F w i T x).2.2.1 j) =
      ∏ j ∈ T, 2 ^ Nat.log2 (x j) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp only [alignmentShortExposureKey, if_pos hj]
  unfold alignmentShortPosteriorKeyGood
  rw [hp, alignmentShortExposureDyadicGood_key]
  rfl

theorem alignment_shortPosterior_badKey_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (T : Finset (Fin n)) :
    Tendsto (fun w => event
      ((globalRawMass (F.cutoff w) (primorial w) n).mapDomain (alignmentShortExposureKey F w i T))
      (fun key => ¬ alignmentShortPosteriorKeyGood F w i T key)) atTop (𝓝 0) := by
  simpa only [event_map, alignmentShortPosteriorKeyGood_key] using
    alignment_typicalShortPosterior_failure_tendsto hF i T

theorem alignment_conditioned_shortPosterior_badKey_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (T : Finset (Fin n))
    (G : ℕ → (Fin n → ℕ) → Prop) {c : ℝ} (hc : 0 < c)
    (hG : ∀ᶠ w in atTop, c ≤ event (globalRawMass (F.cutoff w) (primorial w) n) (G w)) :
    Tendsto (fun w => event
      ((conditionMass (globalRawMass (F.cutoff w) (primorial w) n) (G w)).mapDomain
        (alignmentShortExposureKey F w i T))
      (fun key => ¬ alignmentShortPosteriorKeyGood F w i T key)) atTop (𝓝 0) := by
  simp only [event_map, alignmentShortPosteriorKeyGood_key]
  exact finite_positive_conditioning_zero_limit _ _ _
    ((alignmentGlobalRawMass_geometry hF).mono (fun _ h => h.1)) hc hG
    (alignment_typicalShortPosterior_failure_tendsto hF i T)

end Hindman168
