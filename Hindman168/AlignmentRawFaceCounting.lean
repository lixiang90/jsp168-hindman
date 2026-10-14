import Hindman168.AlignmentCanonicalFaceCounting
import Hindman168.AlignmentRawCanonicalPieces
import Hindman168.AlignmentExposureArrayGoodEvent

namespace Hindman168
open Filter
open scoped Topology Classical

theorem alignment_raw_face_counting_eventually
    {ι : Type*} [Fintype ι] {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (q₀ d : ℕ) (hq : 0 < q₀) (hd : 0 < d) (i : Fin n) (T : Finset (Fin n))
    (c K eps : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (heps : 0 < eps) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support,
      ∀ e : AlignmentAddingPair n i, ∀ a : ι, ∀ L U r : ι → ℤ,
      (∀ j, c * alignmentCubeScale F w i T x ≤ (U j : ℝ) - L j) →
      ∀ f : (ι → ℤ) → ℂ, (∀ z, ‖f z‖ ≤ K) →
      ‖finiteComplexSetMean (alignmentBoxClass L U r d)
          (fun z => f (fun j => z j + if j = a then alignmentPairProgression q₀ w (F.modulus w) e x else 0)) -
        finiteComplexSetMean (alignmentBoxClass L U r d) f‖ ≤ eps := by
  filter_upwards [alignment_canonical_face_counting_eventually (ι := ι) hF q₀ d hq hd i T c K eps hc hK heps,
    alignmentGlobalRawMass_geometry hF] with w hw hg x hx e a L U r hlen f hf
  exact hw x (alignmentGlobalRawMass_support_coprime F w x hx)
    (fun j _ => hg.2.2 x hx j) e a L U r hlen f hf

end Hindman168
