import Hindman168.AlignmentFrozenPieceReading

namespace Hindman168

open FiniteMass Filter
open scoped Topology Classical

theorem alignmentGlobalRawMass_support_coprime {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (x : Fin n → ℕ)
    (hx : x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support) (j : Fin n) :
    Nat.Coprime (x j) (primorial w) := by
  have hne := Finsupp.mem_support_iff.mp hx
  rw [globalRawMass, piMass_apply] at hne
  have hs := Finsupp.mem_support_iff.mpr (Finset.prod_ne_zero_iff.mp hne j (Finset.mem_univ j))
  exact (Finset.mem_filter.mp (rawMass_support_window _ _ hs)).2

theorem alignment_raw_canonical_piece_eventually
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) {q₀ : ℕ} (hq : 0 < q₀)
    (i : Fin n) (C : ℕ) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (V U : Finset (AlignmentAddingPair n i → ℤ)) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support,
      alignmentExposureArrayStable F w i q₀ C T V U x →
      ∀ y ∈ (globalRawMass (F.cutoff w) (primorial w) n).support,
      alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y →
      ∀ v ∈ V, ∀ u ∈ U, ∀ p : ℤ, Int.ModEq (F.modulus w : ℕ) p (y i) →
      |p - y i| ≤ (C * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℕ) →
      intervalResiduePiece (F.gap w i.val) (F.modulus w)
        (alignmentIntegerArrayArgument y (F.modulus w)
          (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
          (fun e => alignmentPairProgression q₀ w (F.modulus w) e y) T p v u) =
        (((alignmentNaturalBlockProduct x T * x i : ℕ) : ℤ) / (F.gap w i.val : ℤ),
          alignmentPivotArrayResidue x T (F.modulus w) (x i)
            (alignmentIntegerSlotShift (fun e => alignmentPairResidue q₀ w (F.modulus w) e x) v)) := by
  filter_upwards [alignmentGlobalRawMass_geometry hF, eventually_ge_atTop (q₀ + 1)] with w hg hw
  intro x hx hgood y hy hkey v hv u hu p hp hdist
  exact alignment_exposure_canonical_piece hF hq hw i C T hT V U hgood
    (alignmentGlobalRawMass_support_coprime F w x hx)
    (alignmentGlobalRawMass_support_coprime F w y hy)
    (fun j _ => hg.2.2 y hy j) hkey v hv u hu p hp hdist

end Hindman168
