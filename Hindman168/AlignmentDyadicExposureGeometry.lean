import Hindman168.BinaryDyadicResidueExposure
import Hindman168.AlignmentShortExposureKey
import Hindman168.AlignmentRawCanonicalPieces
import Hindman168.MasterBinaryDyadicDiscard

namespace Hindman168
open FiniteMass Filter
open scoped Topology Classical

def alignmentShortExposureDyadicGood {n : ℕ} (F : MasterParameterFamily) (w : ℕ)
    (T : Finset (Fin n))
    (key : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ) × ℕ × ℕ) : Prop :=
  ∀ j ∈ T, F.cutoff w j.val ≤ 2 ^ key.2.2.1 j ∧
    2 * 2 ^ key.2.2.1 j ≤ F.cutoff w j.val ^ 2

theorem alignmentShortExposureDyadicGood_key {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ) :
    alignmentShortExposureDyadicGood F w T (alignmentShortExposureKey F w i T x) ↔
      ∀ j ∈ T, binaryDyadicCutoffGood (F.cutoff w j.val) (x j) := by
  simp only [alignmentShortExposureDyadicGood, alignmentShortExposureKey, binaryDyadicCutoffGood]
  exact forall_congr' (fun j => forall_congr' (fun hj => by rw [if_pos hj]))

theorem alignment_shortExposure_tail_window {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) {x y : Fin n → ℕ}
    (hkey : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y)
    (j : Fin n) (hj : j ∈ T) (hy : 0 < y j) :
    y j ∈ binaryDyadicResidueWindow ((F.modulus w : ℕ) * (primorial w) ^ w) (x j) := by
  apply (binaryDyadicResidueWindow_mem hy).mpr
  refine ⟨(alignmentShortExposureKey_dyadic_eq F w i T hkey j hj).symm, ?_⟩
  exact ((alignmentShortExposureKey_rawExposure F w i T hkey).2 j hj).symm

theorem alignment_shortExposure_tail_windows_eventually
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (T : Finset (Fin n)) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support,
      alignmentShortExposureDyadicGood F w T (alignmentShortExposureKey F w i T x) →
      ∀ j ∈ T,
        (binaryDyadicResidueWindow ((F.modulus w : ℕ) * (primorial w) ^ w) (x j)).Nonempty ∧
        binaryDyadicResidueWindow ((F.modulus w : ℕ) * (primorial w) ^ w) (x j) ⊆
          harmonicWindow (F.cutoff w j.val) (primorial w) := by
  filter_upwards [hF.primorial_dvd_modulus] with w hW
  intro x hx hg j hj
  refine ⟨⟨x j, binaryDyadicResidueWindow_anchor
    (alignmentGlobalRawMass_support_positive hF w x hx j)⟩, ?_⟩
  exact binaryDyadicResidueWindow_subset
    ((alignmentShortExposureDyadicGood_key F w i T x).mp hg j hj)
    (hW.trans (dvd_mul_right _ _)) (alignmentGlobalRawMass_support_coprime F w x hx j)

theorem alignment_shortExposure_dyadic_discard_event {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (μ : Mass (Fin n → ℕ)) :
    event (μ.mapDomain (alignmentShortExposureKey F w i T))
      (fun key => ¬ alignmentShortExposureDyadicGood F w T key) =
    event μ (fun x => ∃ j ∈ T, ¬ binaryDyadicCutoffGood (F.cutoff w j.val) (x j)) := by
  simp only [event_map, alignmentShortExposureDyadicGood_key, not_forall, exists_prop]

theorem alignment_shortExposure_dyadic_discard_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (T : Finset (Fin n)) :
    Tendsto (fun w => event
      ((globalRawMass (F.cutoff w) (primorial w) n).mapDomain (alignmentShortExposureKey F w i T))
      (fun key => ¬ alignmentShortExposureDyadicGood F w T key)) atTop (𝓝 0) := by
  simpa only [alignment_shortExposure_dyadic_discard_event] using
    master_global_binaryDyadic_discard_tendsto hF T

end Hindman168
