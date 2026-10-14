import Hindman168.NativeRationalLineDiscrepancy

/-! The UNCONDITIONAL Unit inverse actually produces a character on EVERY
large native short line. One ORIGINAL finite character pool is fixed before
all raw sources, bases, directions and lengths. Both original line tables
and actual nonzero horizontal integrality/operator bounds are retained. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators Classical
universe u

noncomputable def nativeRationalLineCharacterPool {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : ℕ) : Finset (D.E →L[ℝ] ℝ) :=
  ((roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (Q : ℝ)).image
    (fun χ => χ.toContinuousLinearMap)).filter (fun χ => ‖χ‖ ≤ (Q : ℝ))

theorem native_rational_line_character_pool_properties {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : ℕ) (χ : D.E →L[ℝ] ℝ)
    (hχ : χ ∈ nativeRationalLineCharacterPool D Q) :
    RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧ ‖χ‖ ≤ (Q : ℝ) := by
  obtain ⟨hImage,hNorm⟩ := Finset.mem_filter.mp hχ
  obtain ⟨f,hGrid,rfl⟩ := Finset.mem_image.mp hImage
  exact ⟨((rough_native_horizontal_grid_mem_iff D.Γ (Q : ℝ) f).mp hGrid).2,hNorm⟩

theorem native_rational_line_character_production {s ℓ : ℕ} {κ : Type*}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (δ : ℝ) (hδ : 0 < δ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ Q : ℕ, 0 < Q ∧ ∀ (p : RoughVectorMvPolynomial κ D.E),
      RoughVectorMvWeightedDegree L.layer p 0 → ∀ (x : κ → ℤ) (q : κ → ℕ) (T : ℕ), 0 < T →
      ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
      δ ≤ ‖finiteComplexSetMean (Finset.range T) (fun n =>
        F (nativeMvPolynomialOrbit D p (fun j => x j+(q j : ℤ)*(n : ℤ)))-
          ∫ z, F z ∂nativeNilmanifoldQuotientProbability D)‖ →
      ∃ χ ∈ nativeRationalLineCharacterPool D Q,
        (∀ r : ℕ, 0 < r →
          (T : ℝ)^r*‖((MvPolynomial.eval (fun j => (x j : ℝ))
            (scalarMvLineCoefficient (roughVectorMvProjection χ.toLinearMap p)
              (fun j => (q j : ℝ)) r) : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)) ∧
        ∀ I : Unit → ℕ, 0 < (∑ i, I i) →
          (T : ℝ)^(∑ i, I i)*‖((mvPolynomialBinomialCoefficient
            (roughVectorMvProjection χ.toLinearMap (nativeRationalLinePolynomial D p x q)) ℓ I : ℝ) :
              UnitAddCircle)‖ ≤ (Q : ℝ) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨Q,hQ,hInverse⟩ := native_rational_weighted_inverse_unit D L δ hδ
  refine ⟨Q,hQ,?_⟩
  intro p hp x q T hT F hF hBad
  have hNative : δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube Unit T)
      (nativeMvPolynomialOrbit D (nativeRationalLinePolynomial D p x q)) F‖ := by
    rw [native_rational_line_discrepancy_centered D p x q T hT]
    exact hBad
  obtain ⟨χ,hHor,hNorm,hGrid,hMono,hBin⟩ := hInverse _
    (native_rational_line_polynomial_weighted D L p hp x q) T hT F hF hNative
  have hImage : χ ∈ (roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (Q : ℝ)).image
      (fun f => f.toContinuousLinearMap) := by
    apply Finset.mem_image.mpr
    refine ⟨χ.toLinearMap,hGrid,?_⟩
    apply ContinuousLinearMap.ext
    intro v
    rfl
  refine ⟨χ,Finset.mem_filter.mpr ⟨hImage,hNorm⟩,?_,hBin⟩
  intro r hr
  have hPos : 0 < ∑ _i : Unit, r := by simpa only [Finset.univ_unique,Finset.sum_singleton] using hr
  have h := hMono (fun _ => r) hPos
  have hs : Finsupp.equivFunOnFinite.symm (fun _ : Unit => r)=Finsupp.single () r := by
    apply Finsupp.ext
    intro u
    cases u
    simp
  simpa only [Finset.univ_unique,Finset.sum_singleton,hs,native_rational_line_polynomial_coefficient] using h

end Hindman168
