import Hindman168.NativeRationalMultiparameterInverse
import Hindman168.NativePolynomialVariableEquiv
import Hindman168.MvBinomialVariableEquiv

/-! FULL unconditional rational-filtration native inverse for EVERY finite
variable type, including empty types. Literal source/cube/coefficient variable
equivalence preserves the actual original character, grid and BOTH tables. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_weighted_inverse_finite_variables {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (σ : Type*) [Fintype σ] : NativeRationalWeightedInverseStatement D L σ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro δ hδ
  let e := Fintype.equivFin σ
  obtain ⟨Q,hQ,hInverse⟩ := native_rational_weighted_inverse_fin D L (Fintype.card σ) δ hδ
  refine ⟨Q,hQ,?_⟩
  intro p hp N hN F hF hBad
  have hWeight := rough_vector_rename_weighted L.layer L.antitone e hp
  have hBad' : δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube (Fin (Fintype.card σ)) N)
      (nativeMvPolynomialOrbit D (roughVectorMvRename e p)) F‖ := by
    rw [native_polynomial_variable_equiv_cube_discrepancy D e p N F]
    exact hBad
  obtain ⟨χ,hHor,hNorm,hGrid,hMono,hBin⟩ := hInverse _ hWeight N hN F hF hBad'
  refine ⟨χ,hHor,hNorm,hGrid,?_,?_⟩
  · intro I hI
    have hPos : 0 < ∑ j, scalarVariableAssignmentEquiv e ℕ I j := by
      simpa only [scalar_variable_equiv_sum] using hI
    simpa only [rough_vector_rename_projection,scalar_variable_equiv_coefficient,scalar_variable_equiv_sum] using
      hMono (scalarVariableAssignmentEquiv e ℕ I) hPos
  · intro I hI
    have hPos : 0 < ∑ j, scalarVariableAssignmentEquiv e ℕ I j := by
      simpa only [scalar_variable_equiv_sum] using hI
    simpa only [rough_vector_rename_projection,mv_binomial_variable_equiv_coefficient,scalar_variable_equiv_sum] using
      hBin (scalarVariableAssignmentEquiv e ℕ I) hPos

end Hindman168
