import Hindman168.NativeRationalFrozenResidueMean
import Hindman168.IntegerResidueProgressionEnumeration
import Hindman168.NativeRationalProgressionSource
import Hindman168.NativeRationalResidueFiltration

/-! TRUE frozen selected residue cell is EXACTLY a standard integer
progression. ACTUAL affine-substituted source keeps smaller rational
filtration weights/original degree and strict nonlinearity on TRUE
conjugated native data, with GENUINE large mean and original-scale length. -/
namespace Hindman168
open Polynomial MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_frozen_progression_mean {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L K0 : NativeRationalLieFiltration D ℓ)
    (hDrop : nativeRationalFiltrationNonlinearity D K0 < nativeRationalFiltrationNonlinearity D L)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0) (y : D.E)
    (hyRat : y ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) (j : ℕ)
    (A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ K : ℕ, 0 < K ∧ ∀ (M q N : ℕ), 0 < M → 0 < q → 4*K*(M*q) ≤ N →
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ →
      ∀ (z : ℕ → ℤ) (E : ℝ[X]) (p pK : RoughVectorMvPolynomial Unit D.E),
        E.natDegree ≤ j → E.coeff 0=0 → E.coeff 1=0 →
        (∀ i : ℕ, 2 ≤ i → i ≤ j → (M : ℝ)*(N : ℝ)^i*|E.coeff i| ≤ A) →
        RoughVectorMvWeightedDegree K0.layer pK 0 → RoughVectorMvDegreeLE pK ℓ →
        (∀ x : ℝ, nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) p (fun _ => x))=
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval x • y)*
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) pK (fun _ => x))*
              nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval x • y)) →
        ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          δ ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n =>
            nativeRationalTerminalFourierProjection D L k F (nativeMvPolynomialOrbit D p (fun _ => n)))‖ →
          ∃ (a : ℤ) (T m : ℕ) (c : ℝ),
            0 ≤ a ∧ a < (N : ℤ) ∧ 0 < T ∧ m < M*q ∧
            (N : ℝ)/(4*(K : ℝ)*((M*q : ℕ) : ℝ)) ≤ T ∧ |c| ≤ ((j+1 : ℕ) : ℝ)^2*A ∧
            let ρ := nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y)
            let Dm := nativeConjugateNilmanifoldData D ρ
            let Km := nativeRationalResidueFiltration D K0 y hyRat M m
            letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric
            letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric.toUniformSpace.toTopologicalSpace
            let H := nativeConjugateFourierObservable D L k ρ
              (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (c • y)) F
            ∃ pNew : RoughVectorMvPolynomial Unit D.E,
              RoughVectorMvWeightedDegree Km.layer pNew 0 ∧ RoughVectorMvDegreeLE pNew ℓ ∧
              nativeRationalFiltrationNonlinearity Dm Km < nativeRationalFiltrationNonlinearity D L ∧
              (∀ n : ℤ, nativeMvPolynomialOrbit Dm pNew (fun _ => n)=nativeMvPolynomialOrbit Dm pK (fun _ => a+((M*q : ℕ) : ℤ)*n)) ∧
              (∫ q0, H q0 ∂nativeNilmanifoldQuotientProbability Dm)=0 ∧
              δ/2 < ‖finiteComplexSetMean (Finset.Ico 0 (T : ℤ)) (fun n => H (nativeMvPolynomialOrbit Dm pNew (fun _ => n)))‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨K,hK,hSelect⟩ := native_rational_frozen_residue_mean D L k hk y j A δ hA hδ
  refine ⟨K,hK,?_⟩
  intro M q N hM hq hLarge hpow z E p pK hED h0 h1 hBounds hpK hpKD hExact F hF hSignal
  obtain ⟨i,b,a0,m,ha0,hm,hLength,hError,hZero,hMean⟩ :=
    hSelect M q N hM hq hLarge hpow z E p pK hED h0 h1 hBounds hExact F hF hSignal
  have hP : 0 < M*q := Nat.mul_pos hM hq
  have hN : 0 < N := (show 0 < 4*K*(M*q) by positivity).trans_le hLarge
  have hCut := rough_balanced_cut_mono 0 (N : ℤ) K (show i.val ≤ i.val+1 by omega)
  obtain ⟨a,T,hImage,hCard,hMeanImage⟩ := integer_residue_interval_progression
    (roughBalancedCut 0 N K i.val) (roughBalancedCut 0 N K (i.val+1)) (M*q) hP hCut b
  change balancedComplexResidueCell N K (M*q) i b=_ at hImage
  change (balancedComplexResidueCell N K (M*q) i b).card=T at hCard
  have hT : 0 < T := by rw [← hCard]; exact Finset.card_pos.mpr ⟨a0,ha0⟩
  have ha : a ∈ balancedComplexResidueCell N K (M*q) i b := by
    rw [hImage]
    exact Finset.mem_image.mpr ⟨0,Finset.mem_Ico.mpr ⟨le_rfl,by exact_mod_cast hT⟩,by ring⟩
  have hRange := balanced_complex_residue_cell_original_range N K (M*q) hK i b a ha
  have hRange0 := balanced_complex_residue_cell_original_range N K (M*q) hK i b a0 ha0
  let c := E.eval (a0 : ℝ)
  have hC : |c| ≤ ((j+1 : ℕ) : ℝ)^2*A := scalar_nonlinear_small_value_bound E j M N A
    hED h0 h1 hM hN hA hBounds (a0 : ℝ) (by
      rw [abs_of_nonneg (by exact_mod_cast hRange0.1)]
      exact_mod_cast hRange0.2.le)
  let ρ := nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y)
  let Dm := nativeConjugateNilmanifoldData D ρ
  let Km := nativeRationalResidueFiltration D K0 y hyRat M m
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric.toUniformSpace.toTopologicalSpace
  let H := nativeConjugateFourierObservable D L k ρ
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (c • y)) F
  let pNew := nativeRationalProgressionPolynomial D pK a (M*q)
  have hWeights : RoughVectorMvWeightedDegree Km.layer pNew 0 :=
    native_rational_residue_filtration_weighted D K0 y hyRat M m pNew
      (native_rational_progression_polynomial_weighted D K0 pK hpK a (M*q))
  have hDegree : RoughVectorMvDegreeLE pNew ℓ := native_rational_progression_polynomial_degree D pK ℓ hpKD a (M*q)
  have hOrbit (n : ℤ) : nativeMvPolynomialOrbit Dm pNew (fun _ => n)=
      nativeMvPolynomialOrbit Dm pK (fun _ => a+((M*q : ℕ) : ℤ)*n) :=
    native_rational_progression_polynomial_orbit Dm pK a (M*q) n
  refine ⟨a,T,m,c,hRange.1,hRange.2,hT,hm,by rw [← hCard]; exact hLength,hC,pNew,hWeights,hDegree,
    native_rational_residue_filtration_nonlinearity_lt D L K0 hDrop y hyRat M m,hOrbit,hZero,?_⟩
  have hTransfer := hMeanImage (fun n => H (nativeMvPolynomialOrbit Dm pK (fun _ => n)))
  change finiteComplexSetMean (balancedComplexResidueCell N K (M*q) i b)
      (fun n => H (nativeMvPolynomialOrbit Dm pK (fun _ => n)))=_ at hTransfer
  have hMeanTyped : δ/2 < ‖finiteComplexSetMean (balancedComplexResidueCell N K (M*q) i b)
      (fun n => H (nativeMvPolynomialOrbit Dm pK (fun _ => n)))‖ := hMean
  have he : (fun n : ℤ => H (nativeMvPolynomialOrbit Dm pK (fun _ => a+((M*q : ℕ) : ℤ)*n)))=
      (fun n : ℤ => H (nativeMvPolynomialOrbit Dm pNew (fun _ => n))) := by
    funext n
    exact congrArg H (hOrbit n).symm
  exact hMeanTyped.trans_eq (congrArg norm (hTransfer.trans
    (congrArg (finiteComplexSetMean (Finset.Ico 0 (T : ℤ))) he)))

end Hindman168
