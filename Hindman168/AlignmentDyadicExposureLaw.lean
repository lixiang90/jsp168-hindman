import Hindman168.AlignmentDyadicExposureGeometry
import Hindman168.FiniteSupportedConditioning
import Hindman168.DyadicHarmonicTailLaw
import Hindman168.FinitePositiveConditioningLimit

namespace Hindman168
open FiniteMass Filter
open scoped Topology Classical

theorem alignment_dyadic_residue_condition_exact
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (w : ℕ) (T : Finset (Fin n)) (x : Fin n → ℕ) :
    conditionMass (globalRawMass (F.cutoff w) (primorial w) n)
      (fun y => ∀ j ∈ T, Nat.log2 (y j) = Nat.log2 (x j) ∧
        y j % ((F.modulus w : ℕ) * (primorial w) ^ w) =
          x j % ((F.modulus w : ℕ) * (primorial w) ^ w)) =
    conditionMass (globalRawMass (F.cutoff w) (primorial w) n)
      (fun y => ∀ j ∈ T, y j ∈ binaryDyadicResidueWindow
        ((F.modulus w : ℕ) * (primorial w) ^ w) (x j)) := by
  apply conditionMass_congr_on_support
  intro y hy
  exact forall_congr' (fun j => forall_congr' (fun _ =>
    (binaryDyadicResidueWindow_mem (alignmentGlobalRawMass_support_positive hF w y hy j)).symm))

theorem alignment_dyadic_residue_condition_product
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (w : ℕ) (T : Finset (Fin n)) (x : Fin n → ℕ) :
    conditionMass (globalRawMass (F.cutoff w) (primorial w) n)
      (fun y => ∀ j ∈ T, Nat.log2 (y j) = Nat.log2 (x j) ∧
        y j % ((F.modulus w : ℕ) * (primorial w) ^ w) =
          x j % ((F.modulus w : ℕ) * (primorial w) ^ w)) =
    piMass (fun j : Fin n => conditionMass (rawMass (F.cutoff w j.val) (primorial w))
      (fun p => j ∈ T → p ∈ binaryDyadicResidueWindow
        ((F.modulus w : ℕ) * (primorial w) ^ w) (x j))) := by
  rw [alignment_dyadic_residue_condition_exact hF, globalRawMass,
    piMass_conditionMass, conditionMass,
    event_piMass_all _ (fun j p => j ∈ T → p ∈ binaryDyadicResidueWindow
      ((F.modulus w : ℕ) * (primorial w) ^ w) (x j))]
  rfl

theorem alignment_conditioned_dyadic_exposure_discard_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (T : Finset (Fin n))
    (G : ℕ → (Fin n → ℕ) → Prop) {c : ℝ} (hc : 0 < c)
    (hG : ∀ᶠ w in atTop, c ≤ event (globalRawMass (F.cutoff w) (primorial w) n) (G w)) :
    Tendsto (fun w => event
      ((conditionMass (globalRawMass (F.cutoff w) (primorial w) n) (G w)).mapDomain
        (alignmentShortExposureKey F w i T))
      (fun key => ¬ alignmentShortExposureDyadicGood F w T key)) atTop (𝓝 0) := by
  simp only [alignment_shortExposure_dyadic_discard_event]
  exact finite_positive_conditioning_zero_limit _ _ _
    ((alignmentGlobalRawMass_geometry hF).mono (fun _ h => h.1)) hc hG
    (master_global_binaryDyadic_discard_tendsto hF T)

end Hindman168
