import Hindman168.NativeRationalCharacterChildBudget
import Hindman168.NativeRationalResidueInverseBudget
import Hindman168.NativeRationalConstructedChildInverseTransport

/-! The ACTUAL fixed good-character branch closes to an ORIGINAL full
inverse conclusion from strictly smaller NONLINEARITY IH. Child inverse
budgets precede all raw sources. This is a genuine induction STEP, not the
unconditional higher-degree inverse or a supplied inverse for one kernel. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

def NativeRationalCharacterOriginalBudget {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (A δ : ℝ) (S : ℕ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (B Q : ℕ) : Prop :=
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ M : ℕ, 0 < M → M ≤ S → ∀ (p : RoughVectorMvPolynomial Unit D.E)
      (hp : RoughVectorMvWeightedDegree L.layer p 0) (N : ℕ), B ≤ N →
      (∀ i : ℕ, 2 ≤ i → i ≤ ℓ → (N : ℝ)^i*
        ‖(((M : ℝ)*(nativeRationalCompactNonlinearScalar D L p hp χ).coeff i : ℝ) : UnitAddCircle)‖ ≤ A) →
      ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        δ ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n =>
          nativeRationalTerminalFourierProjection D L k F (nativeMvPolynomialOrbit D p (fun _ => n)))‖ →
        ∃ κ : D.E →L[ℝ] ℝ,
          RoughNativeHorizontalFunctional (I := D.I) D.Γ κ.toLinearMap ∧ ‖κ‖ ≤ (Q : ℝ) ∧
          κ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (Q : ℝ) ∧
          (∀ I : Unit → ℕ, 0 < (∑ i, I i) →
            (N : ℝ)^(∑ i, I i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
              (roughVectorMvProjection κ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)) ∧
          ∀ I : Unit → ℕ, 0 < (∑ i, I i) →
            (N : ℝ)^(∑ i, I i)*‖((mvPolynomialBinomialCoefficient
              (roughVectorMvProjection κ.toLinearMap p) ℓ I : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)

theorem native_rational_character_original_budget_mono {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (A δ : ℝ) (S : ℕ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (B Q Q' : ℕ) (hQQ : Q ≤ Q')
    (hData : NativeRationalCharacterOriginalBudget D L k A δ S χ B Q) :
    NativeRationalCharacterOriginalBudget D L k A δ S χ B Q' := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro M hM hMS p hp N hBN hBounds F hF hSignal
  obtain ⟨κ,hHor,hNorm,_hGrid,hMono,hBin⟩ := hData M hM hMS p hp N hBN hBounds F hF hSignal
  have hBudget : (Q : ℝ) ≤ (Q' : ℝ) := by exact_mod_cast hQQ
  have hn := hNorm.trans hBudget
  exact ⟨κ,hHor,hn,
    rough_native_norm_bounded_horizontal_grid_mem D.Γ (Q' : ℝ) (Nat.cast_nonneg Q') κ hn hHor,
    fun I hI => (hMono I hI).trans hBudget,fun I hI => (hBin I hI).trans hBudget⟩

theorem native_rational_character_inverse_induction {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (hIH : ∀ (D' : NativeNilmanifoldData.{u} s) (L' : NativeRationalLieFiltration D' ℓ),
      nativeRationalFiltrationNonlinearity D' L' < nativeRationalFiltrationNonlinearity D L →
      NativeRationalWeightedInverseStatement D' L' Unit)
    (k : nativeRationalTerminalIndex D L → ℤ) (A δ : ℝ) (S : ℕ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (B : ℕ) (θ : ℝ)
    (hB : 0 < B) (hθ : 0 < θ) (hA : 0 ≤ A)
    (hData : NativeRationalCharacterChildBudget D L k A δ S χ B θ) :
    ∃ Q : ℕ, 0 < Q ∧ NativeRationalCharacterOriginalBudget D L k A δ S χ B Q := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨hHor,hzero,hDiff,j,y,q,K,_hj2,_hjL,_hy,hyRat,_hFy,_hHigher,hq,hPower,_hK,
    hqB,_hKB,hyB,_h4B,hSelect⟩ := hData
  let K0 := nativeRationalNonlinearKernelFiltration D L χ hHor hzero
  have hDrop : nativeRationalFiltrationNonlinearity D K0 < nativeRationalFiltrationNonlinearity D L :=
    native_rational_nonlinear_kernel_filtration_nonlinearity_lt D L hdeg χ hHor hzero hDiff
  obtain ⟨CK,hCK,hChild⟩ := native_rational_residue_inverse_budget D L K0 hDrop hIH y hyRat S q
    (θ/2) (by positivity)
  obtain ⟨Q,hQ,hTransport⟩ := native_rational_constructed_child_inverse_transport D ℓ S B
    (CK : ℝ) A (CK : ℝ) hB (Nat.cast_nonneg CK) hA (Nat.cast_nonneg CK)
  refine ⟨Q,hQ,?_⟩
  intro M hM hMS p hp N hBN hBounds F hF hSignal
  obtain ⟨a,T,m,ha0,haN,hT,hm,hLength,Km,hLayers,_hDropNew,pNew,hW,_hD,
    ⟨z,E,pK,hED,_hEZero,hEOne,hError,_hKW,hKD,hExact,hConstructed,_hOrbit⟩,J,hJ,hBad⟩ :=
    hSelect M hM hMS p hp N hBN hBounds F hF hSignal
  let ρ := nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y)
  let Dm := nativeConjugateNilmanifoldData D ρ
  let Kcanon := nativeRationalResidueFiltration D K0 y hyRat M m
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric.toUniformSpace.toTopologicalSpace
  have hCanonical : RoughVectorMvWeightedDegree Kcanon.layer pNew 0 := by
    intro term ht
    change term.2 ∈ K0.layer (term.1.totalDegree+0)
    rw [← hLayers]
    exact hW term ht
  obtain ⟨κ,hHorChild,hNorm,_hGridChild,hMonoChild,_hBinChild⟩ :=
    hChild M hMS m hm pNew hCanonical T hT J hJ
      ((show θ/2 ≤ θ by linarith only [hθ]).trans hBad.le)
  have hN : 0 < N := hB.trans_le hBN
  exact hTransport M q hM hMS hq hqB ρ κ hHorChild hNorm y hyB p pK pNew j N T a z E
    hN ha0 haN hLength hKD hConstructed hED hEOne hError hPower hExact hMonoChild

end Hindman168
