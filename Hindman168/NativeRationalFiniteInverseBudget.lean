import Hindman168.NativeRationalWeightedInverseStatement
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A finite family of ACTUAL full native inverse theorems receives one
positive original character/grid/two-table budget BEFORE all raw sources.
The family premises are to be supplied by genuine smaller-measure IH. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_rational_finite_inverse_budget {s ℓ : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s)
    (L : ∀ i, NativeRationalLieFiltration (D i) ℓ)
    (hInverse : ∀ i, NativeRationalWeightedInverseStatement (D i) (L i) Unit)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℕ, 0 < C ∧ ∀ i : ι,
      letI : MeasurableSpace (D i).E := borel (D i).E
      letI : MeasurableSpace (D i).G := borel (D i).G
      letI := (D i).metric
      letI : TopologicalSpace ((D i).G ⧸ (D i).Γ) := (D i).metric.toUniformSpace.toTopologicalSpace
      ∀ p : RoughVectorMvPolynomial Unit (D i).E,
      RoughVectorMvWeightedDegree (L i).layer p 0 → ∀ N : ℕ, 0 < N →
      ∀ H ∈ unitLipschitzObservables ((D i).G ⧸ (D i).Γ),
        δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy (D i) (scalarMvIntegerCube Unit N)
          (nativeMvPolynomialOrbit (D i) p) H‖ →
        ∃ χ : (D i).E →L[ℝ] ℝ,
          RoughNativeHorizontalFunctional (I := (D i).I) (D i).Γ χ.toLinearMap ∧ ‖χ‖ ≤ (C : ℝ) ∧
          χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := (D i).I) (D i).Γ (C : ℝ) ∧
          (∀ J : Unit → ℕ, 0 < (∑ j, J j) →
            (N : ℝ)^(∑ j, J j)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
              (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (C : ℝ)) ∧
          ∀ J : Unit → ℕ, 0 < (∑ j, J j) →
            (N : ℝ)^(∑ j, J j)*‖((mvPolynomialBinomialCoefficient
              (roughVectorMvProjection χ.toLinearMap p) ℓ J : ℝ) : UnitAddCircle)‖ ≤ (C : ℝ) := by
  have hEach (i : ι) := hInverse i δ hδ
  choose n hn hData using hEach
  let C := 1+∑ i, n i
  have hC : 0 < C := by dsimp only [C]; omega
  have hnC (i : ι) : n i ≤ C :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (by dsimp only [C]; omega)
  refine ⟨C,hC,?_⟩
  intro i
  letI : MeasurableSpace (D i).E := borel (D i).E
  letI : MeasurableSpace (D i).G := borel (D i).G
  letI := (D i).metric
  letI : TopologicalSpace ((D i).G ⧸ (D i).Γ) := (D i).metric.toUniformSpace.toTopologicalSpace
  intro p hp N hN H hH hBad
  obtain ⟨χ,hHor,hNorm,_hGrid,hMono,hBin⟩ := hData i p hp N hN H hH hBad
  have hBudget : (n i : ℝ) ≤ (C : ℝ) := by exact_mod_cast hnC i
  have hNormC := hNorm.trans hBudget
  exact ⟨χ,hHor,hNormC,
    rough_native_norm_bounded_horizontal_grid_mem (D i).Γ (C : ℝ) (Nat.cast_nonneg C) χ hNormC hHor,
    fun J hJ => (hMono J hJ).trans hBudget,fun J hJ => (hBin J hJ).trans hBudget⟩

end Hindman168
