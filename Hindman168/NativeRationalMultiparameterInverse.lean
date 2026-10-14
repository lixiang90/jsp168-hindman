import Hindman168.NativeRationalMultiparameterLargeInverse
import Hindman168.NativeRationalLargeMvToAllLengths

/-! UNCONDITIONAL corrected native multiparameter equal-cube inverse for
EVERY original degree/dimension and positive sample length. True native line
construction, proved Unit/scalar inverses, common-character/multiplier/direction
reconstruction and actual constant anchors supply all former analytic inputs.
Original nonzero/grid/norm character and BOTH complete raw tables survive. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_weighted_inverse_fin {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (n : ℕ) :
    NativeRationalWeightedInverseStatement D L (Fin n) := by
  by_cases h0 : ℓ=0
  · subst ℓ
    exact native_rational_weighted_inverse_degree_zero D L (Fin n)
  have hℓ : 1 ≤ ℓ := by omega
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro δ hδ
  let η := min δ 1
  have hη : 0 < η := lt_min hδ (by norm_num)
  have hη1 : η ≤ 1 := min_le_right _ _
  obtain ⟨Q,T,_hQ,hT,hLarge⟩ := native_rational_multiparameter_large_inverse (n := n) D L hℓ η hη hη1
  obtain ⟨R,hR,hAll⟩ := native_rational_large_mv_inverse_to_all_lengths (σ := Fin n) D L η Q T hT hLarge
  refine ⟨R,hR,?_⟩
  intro p hp N hN F hF hBad
  exact hAll p hp N hN F hF ((min_le_left δ 1).trans hBad)

end Hindman168
