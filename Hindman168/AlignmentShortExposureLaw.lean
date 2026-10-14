import Hindman168.AlignmentShortExposureFibers
import Hindman168.FiniteSupportedConditioning

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

theorem sameNaturalShortBin_iff {V : ℕ} (hV : 0 < V) (a b : ℕ) :
    a / V = b / V ↔ (a / V) * V ≤ b ∧ b < (a / V) * V + V := by
  rw [eq_comm, Nat.div_eq_iff hV]
  omega

theorem alignment_shortExposure_condition_exact
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (w : ℕ) (i : Fin n) (T : Finset (Fin n))
    (x : Fin n → ℕ)
    (hR : 0 < alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) :
    let V := (∏ j ∈ T, 2 ^ Nat.log2 (x j)) *
      alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)
    let Q := (alignmentNaturalBlockProduct x T * x i / V) * V
    conditionMass (globalRawMass (F.cutoff w) (primorial w) n)
      (fun y => alignmentShortExposureKey F w i T y = alignmentShortExposureKey F w i T x) =
    conditionMass (globalRawMass (F.cutoff w) (primorial w) n)
      (fun y => (∀ j, j < i → j ∉ T → x j = y j) ∧
        (∀ j ∈ T, y j ∈ binaryDyadicResidueWindow ((F.modulus w : ℕ) * (primorial w) ^ w) (x j)) ∧
        y i % (F.modulus w : ℕ) = x i % (F.modulus w : ℕ) ∧
        Q ≤ alignmentNaturalBlockProduct y T * y i ∧
        alignmentNaturalBlockProduct y T * y i < Q + V) := by
  dsimp only
  have hV : 0 < (∏ j ∈ T, 2 ^ Nat.log2 (x j)) *
      alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) := by positivity
  apply conditionMass_congr_on_support
  intro y hy
  have hf := alignmentShortExposureKey_window_iff F w i T x y
    (fun j _ => alignmentGlobalRawMass_support_positive hF w y hy j)
  rw [eq_comm] at hf
  rw [hf]
  constructor
  · rintro ⟨hout, hwin, hp, hb⟩
    exact ⟨hout, hwin, hp.symm, (sameNaturalShortBin_iff hV _ _).mp hb⟩
  · rintro ⟨hout, hwin, hp, hb⟩
    exact ⟨hout, hwin, hp.symm, (sameNaturalShortBin_iff hV _ _).mpr hb⟩

end Hindman168
