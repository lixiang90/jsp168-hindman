import Hindman168.PositivePrincipalSumFutureEvent
import Hindman168.PositivePrincipalSumFutureThresholdPaths

namespace Hindman168
open scoped Classical

/-- A successful sequence of actual future-protected pivot transitions
already has the native threshold event required by the integer adapter.
The final-scale membership is deduced from its actual frontier path. -/
theorem principal_native_threshold_path_event {n M r : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (F : MasterParameterFamily)
    (schedule : List (AlignmentPlannedPivot n))
    (hcover : schedule.map AlignmentPlannedPivot.pivot = List.finRange n)
    (bstart : Fin n → ℚ) (A : Finset ℚ)
    (hclosed : FiniteScaleClosure (alignmentScheduleFinalScales schedule {bstart}) A)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (q₀ w : ℕ) (x : Fin M → ℕ) (θ : ℝ) (bfin : Fin n → ℚ)
    (hpath : PrincipalThresholdScalePath
      (fun i => Multiplicative (AlignmentAddingPair M (principalAlignmentEmbedding e heM i) → ℤ))
      (fun i => Multiplicative (AlignmentAddingPair M (principalAlignmentEmbedding e heM i) → ℤ))
      (Fin r) q₀ (fun _ => principalNativeLetter (principalAlignmentEmbedding e heM))
      (principalNativeScaleObservation e heM F A S q₀ w x) θ (fun _ => 1)
      schedule bstart bfin) :
    PrincipalNativeThresholdEvent e heM F (alignmentScheduleFinalScales schedule {bstart})
      A hclosed S q₀ θ w x := by
  obtain ⟨hmem, hrequests⟩ := principal_threshold_path_final _ _ _ q₀ _ _ θ _ hcover hpath
  exact ⟨⟨bfin, hmem⟩, hrequests⟩
end Hindman168
