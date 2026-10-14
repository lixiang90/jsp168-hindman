import Hindman168.AlignmentRetainedScaleGrowth
import Hindman168.AlignmentExposureArrayGoodEvent

namespace Hindman168
open Filter
open scoped Topology

theorem alignment_raw_retained_scale_eventually
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (p : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support,
      ∀ U : Finset (Fin n), U ⊆ T → ∀ j ∈ T,
      ((2 ^ Nat.log2 (x j) : ℕ) : ℝ) ^ p ≤ eps *
        (alignmentCubeScale F w i T x / ((d : ℝ) * alignmentNaturalBlockProduct x U)) := by
  filter_upwards [alignment_tail_factor_scale_eventually hF i T hT d hd p heps,
    alignmentGlobalRawMass_geometry hF] with w hw hg x hx U hU j hj
  exact hw x (fun l _ => alignmentGlobalRawMass_support_positive hF w x hx l)
    (fun l _ => hg.2.2 x hx l) U hU j hj

theorem alignment_raw_retained_scale_powerDominates
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (x : ℕ → Fin n → ℕ)
    (U : ℕ → Finset (Fin n)) (j : ℕ → Fin n)
    (hvalid : ∀ᶠ w in atTop, x w ∈ (globalRawMass (F.cutoff w) (primorial w) n).support ∧
      U w ⊆ T ∧ j w ∈ T) :
    PowerDominates atTop
      (fun w => alignmentCubeScale F w i T (x w) / ((d : ℝ) * alignmentNaturalBlockProduct (x w) (U w)))
      (fun w => ((2 ^ Nat.log2 (x w (j w)) : ℕ) : ℝ)) := by
  apply alignment_tail_factor_scale_powerDominates hF i T hT d hd x U j
  filter_upwards [hvalid, alignmentGlobalRawMass_geometry hF] with w hv hg
  exact ⟨fun l _ => alignmentGlobalRawMass_support_positive hF w (x w) hv.1 l,
    (fun l _ => hg.2.2 (x w) hv.1 l), hv.2⟩

end Hindman168
