import Hindman168.NativeRationalLargeInverseInduction
import Hindman168.NativeRationalLargeToAllLengths

/-! FULL native Unit inverse induction STEP, including every ORIGINAL
positive sample length and both complete coefficient tables. Its only inverse
premises are true lower-degree and strictly smaller-nonlinearity IH. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_full_inverse_induction_step {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (hLower : NativeRationalWeightedInverseStatement (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit)
    (hZero : NativeRationalWeightedInverseStatement (nativeRationalTerminalQuotientData D L)
      (nativeTerminalRationalLieFiltration D L) Unit)
    (hIH : ∀ (D' : NativeNilmanifoldData.{u} s) (L' : NativeRationalLieFiltration D' ℓ),
      nativeRationalFiltrationNonlinearity D' L' < nativeRationalFiltrationNonlinearity D L →
      NativeRationalWeightedInverseStatement D' L' Unit) :
    NativeRationalWeightedInverseStatement D L Unit := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro δ hδ
  obtain ⟨Q,T,_hQ,hT,hLarge⟩ := native_rational_large_inverse_induction D L hdeg hLower hZero hIH δ hδ
  exact native_rational_large_inverse_to_all_lengths D L δ Q T hT hLarge

end Hindman168
