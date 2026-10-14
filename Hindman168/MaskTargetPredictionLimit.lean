import Hindman168.MaskTargetPredictionData

/-! The existing proved original prediction cube theorem applies to the
actual target denominator and original quotient intervals. No desired
small cube mean is a hypothesis of this source application. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

include hJ hgap in
theorem targetPredictionAverage_tendsto_zero
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    Tendsto (targetPredictionAverage gap C hC t J label) atTop (𝓝 0) := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  let d := targetPredictionOrder gap t
  let dir := allPredictionCubeDirections 1 d
  let lab : ℕ → ReplicaCubeRow 1 d → Fin (m + 1) := fun w _ => label w none
  let tail := fun w => Finset.range (gap w).val
  let s : ℕ → Fin 1 → ℕ := fun w _ => ((maskGeneratedMaster m gap).modulus w : ℕ)
  let f : Fin 1 → MvPolynomial (Fin (maskGeneratedRowDataFamily m gap t).arity) ℤ :=
    fun _ => targetPredictionPolynomial gap t
  let G : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → ReplicaCubeRow 1 d → ℤ → ℝ :=
    fun w _ _ => targetRootCenteredMask gap C t label w
  have htailLab : ∀ᶠ w in atTop, ∀ base, (C w).tail (lab w base) ⊆ tail w :=
    htail.mono (fun _ hw _ => hw _)
  have htailRoot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (targetPredictionRoot gap C hC t w).val :=
    hgap.mono (fun _ hw => Finset.range_mono (hw _))
  have hbound : ∀ᶠ w in atTop, ∀ x i y, |G w x (some (dir i)) y| ≤
      1 + integerDivisorMask (masterPredictionBaseDivisorMass (maskGeneratedMaster m gap) C lab w (some (dir i))) y := by
    filter_upwards [masks_eventually_bounded gap C hC t htail label] with w hw
    intro x i y
    change |integerDivisorMask (tailMass (primorial w)
      ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1| ≤ _
    have he := abs_sub (integerDivisorMask (tailMass (primorial w)
      ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y) (1 : ℝ)
    rw [abs_of_nonneg (hw none y).1, abs_one] at he
    exact he.trans_eq (by unfold masterPredictionBaseDivisorMass; dsimp [lab]; ring)
  unfold targetPredictionAverage
  exact hF.prediction_quotient_cube_product_tendsto dir (allPredictionCubeDirections_bijective 1 d)
    C hC lab tail htailLab (targetPredictionRoot gap C hC t)
    (fun (w : ℕ) (_ : Fin 1) => gap w) (fun (w : ℕ) (_ : Fin (maskGeneratedRowDataFamily m gap t).arity) => gap w)
    J (by omega) htailRoot (Eventually.of_forall (fun _ _ => Finset.Subset.refl _))
    (Eventually.of_forall (fun _ _ => Finset.Subset.refl _))
    (hgap.mono (fun _ hw _ => hw _)) {targetPredictionPolynomial gap t}
    (by intro p hp; rw [Finset.mem_singleton] at hp; subst p; exact targetPredictionPolynomial_ne_zero gap t)
    s (Eventually.of_forall (fun _ _ => dvd_refl _))
    (hF.primorial_dvd_modulus.mono (fun _ hw _ => hw)) f (fun _ => Finset.mem_singleton_self _)
    (fun _ _ _ => 0) (maskGeneratedCopiedPrimeGood m gap t)
    (Eventually.of_forall (fun _ _ _ _ => rfl))
    (Eventually.of_forall (fun w x _ hx _ => targetPrediction_good_den_nonzero gap t w x hx))
    G (fun _ _ => rfl) hbound

end Hindman168.MaskOriginalSampling
