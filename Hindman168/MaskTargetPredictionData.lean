import Hindman168.MaskTargetUnrestrictedTransfer
import Hindman168.MasterPredictionQuotientCubeLimit
import Hindman168.SingleCubeVertexTransport

/-! Concrete one-replica prediction data for the original target cube.
Its modulus and quotient length are exactly those already used in the
mask-generated direction law, with the same original good-prime event. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open scoped BigOperators Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))

noncomputable def targetPredictionOrder : ℕ :=
  Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)

noncomputable def targetPredictionRoot (w : ℕ) : Fin N :=
  ⟨(C w).pivot (targetRootAnchor gap t),
    Finset.mem_range.mp (hC w (targetRootAnchor gap t) (by simp [Chain.block]))⟩

noncomputable def targetPredictionPolynomial : MvPolynomial (Fin (maskGeneratedRowDataFamily m gap t).arity) ℤ :=
  (maskGeneratedRowDataFamily m gap t).rows.denominator (maskGeneratedRowDataFamily m gap t).target

noncomputable def targetRootCenteredMask
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) (w : ℕ) (y : ℤ) : ℝ :=
  integerDivisorMask (tailMass (primorial w)
    ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1

noncomputable def targetPredictionAverage (J : ℕ)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) : ℕ → ℝ :=
  masterPredictionOriginalCubeAverage (maskGeneratedMaster m gap) (targetPredictionRoot gap C hC t)
    (fun w _ => (gap w).val) (fun (w : ℕ) (_ : Fin 1) => ((maskGeneratedMaster m gap).modulus w : ℕ))
    (fun _ : Fin 1 => targetPredictionPolynomial gap t) (fun _ _ _ => 0)
    (predictionQuotientLength (maskGeneratedMaster m gap) (fun (w : ℕ) (_ : Fin 1) => gap w) J
      (fun (w : ℕ) (_ : Fin 1) => ((maskGeneratedMaster m gap).modulus w : ℕ))
      (fun _ : Fin 1 => targetPredictionPolynomial gap t))
    (maskGeneratedCopiedPrimeGood m gap t)
    (fun w _ (_ : ReplicaCubeRow 1 (targetPredictionOrder gap t)) => targetRootCenteredMask gap C t label w)

theorem targetPredictionPolynomial_ne_zero : targetPredictionPolynomial gap t ≠ 0 :=
  (maskGeneratedRowDataFamily m gap t).rows.denominator_ne_zero _

theorem targetPredictionModulus_eq_actual (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) :
    predictionCubeModulus w ((maskGeneratedMaster m gap).modulus w : ℕ) (targetPredictionPolynomial gap t) x =
      ((maskGeneratedRowDataFamily m gap t).rows.translationModulus
        (maskGeneratedMaster m gap) w x (maskGeneratedRowDataFamily m gap t).target : ℤ) := by
  unfold predictionCubeModulus PolynomialRowFamily.translationModulus targetPredictionPolynomial
  rw [Int.natCast_mul]

theorem targetPredictionQuotientLength_eq_actual (J w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) (q : Fin 1) :
    predictionQuotientLength (maskGeneratedMaster m gap) (fun (w : ℕ) (_ : Fin 1) => gap w) J
      (fun (w : ℕ) (_ : Fin 1) => ((maskGeneratedMaster m gap).modulus w : ℕ))
      (fun _ : Fin 1 => targetPredictionPolynomial gap t) w x q = maskGeneratedShiftLength m gap t J w x := by
  unfold predictionQuotientLength maskGeneratedShiftLength
  rw [targetPredictionModulus_eq_actual, Int.natAbs_natCast]

theorem targetPrediction_good_den_nonzero (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (hx : maskGeneratedCopiedPrimeGood m gap t w x) :
    MvPolynomial.eval (fun j => (x j : ℤ)) (targetPredictionPolynomial gap t) ≠ 0 :=
  predictionLocalPrimeGoodEvent_den_nonzero _ _ _
    ((maskGeneratedRowDataFamily m gap t).rows.denominator_mem_catalog _) w x hx.2

end Hindman168.MaskOriginalSampling
