import Hindman168.NativeRationalRightSampleFreezing
import Hindman168.NativeRationalIntegerResidueCoset
import Hindman168.BalancedComplexResidueGeometry
import Hindman168.FiniteComplexSampleStability
import Hindman168.NativeCentralPolynomialProjection

/-! A GENUINE original Fourier signal selects an ACTUAL short residue cell
with original-scale positive length, a TRUE finite right representative,
REAL freezing error and LARGE frozen mean on actual conjugated native data.
The fixed block budget precedes ALL raw sources/M/q/N. -/
namespace Hindman168
open Polynomial MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_frozen_residue_mean {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0) (y : D.E) (j : ℕ)
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
        (∀ x : ℝ, nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) p (fun _ => x))=
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval x • y)*
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) pK (fun _ => x))*
              nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval x • y)) →
        ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          δ ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n =>
            nativeRationalTerminalFourierProjection D L k F (nativeMvPolynomialOrbit D p (fun _ => n)))‖ →
          ∃ (i : Fin K) (b : Fin (M*q)) (a : ℤ) (m : ℕ),
            a ∈ balancedComplexResidueCell N K (M*q) i b ∧ m < M*q ∧
            (N : ℝ)/(4*(K : ℝ)*((M*q : ℕ) : ℝ)) ≤ (balancedComplexResidueCell N K (M*q) i b).card ∧
            let ρ := nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y)
            letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
            letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
              (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
            let H := nativeConjugateFourierObservable D L k ρ
              (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval (a : ℝ) • y)) F
            (∀ n ∈ balancedComplexResidueCell N K (M*q) i b,
              ‖nativeRationalTerminalFourierProjection D L k F (nativeMvPolynomialOrbit D p (fun _ => n))-
                H (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
                  (roughVectorMvEval (E := D.E) pK (fun _ => (n : ℝ))) : D.G ⧸ roughConjugateSubgroup D.Γ ρ)‖ < δ/4) ∧
            (∫ q0, H q0 ∂nativeNilmanifoldQuotientProbability (nativeConjugateNilmanifoldData D ρ))=0 ∧
            δ/2 < ‖finiteComplexSetMean (balancedComplexResidueCell N K (M*q) i b) (fun n =>
              H (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
                (roughVectorMvEval (E := D.E) pK (fun _ => (n : ℝ))) : D.G ⧸ roughConjugateSubgroup D.Γ ρ))‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨r,hr,_hr1,hFreeze⟩ := native_rational_right_sample_freezing D L k y j A (δ/4) hA (by positivity)
  let K := ⌈2/r⌉₊+1
  have hK : 0 < K := by dsimp only [K]; omega
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hRadius : 2/(K : ℝ) ≤ r := by
    have hh : 2/r ≤ (K : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ ⌈2/r⌉₊)
    have hh' := (div_le_iff₀ hr).mp hh
    apply (div_le_iff₀ hKr).mpr
    nlinarith
  refine ⟨K,hK,?_⟩
  intro M q N hM hq hLarge hpow z E p pK hED h0 h1 hBounds hExact F hF hSignal
  have hP : 0 < M*q := Nat.mul_pos hM hq
  have hN : 0 < N := (show 0 < 4*K*(M*q) by positivity).trans_le hLarge
  have hTwo : 2*K ≤ N := by have hp : 1 ≤ M*q := hP; nlinarith
  let f : ℤ → ℂ := fun n => nativeRationalTerminalFourierProjection D L k F (nativeMvPolynomialOrbit D p (fun _ => n))
  obtain ⟨i,b,hCell,hLength,hMean⟩ := balanced_complex_residue_mean_selection N K (M*q) hK hP hLarge f
  obtain ⟨a,ha⟩ := hCell
  have hA0 := balanced_complex_residue_cell_original_range N K (M*q) hK i b a ha
  obtain ⟨m,hm,hResidueA⟩ := native_rational_polynomial_finite_residue D j M q z y hM hq hpow a.toNat
  have hAR : (a.toNat : ℝ)=(a : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hA0.1
  rw [hAR] at hResidueA
  let ρ := nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y)
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
    (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
  let H := nativeConjugateFourierObservable D L k ρ
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval (a : ℝ) • y)) F
  let g : ℤ → ℂ := fun n => H (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
    (roughVectorMvEval (E := D.E) pK (fun _ => (n : ℝ))) : D.G ⧸ roughConjugateSubgroup D.Γ ρ)
  have hError : ∀ n ∈ balancedComplexResidueCell N K (M*q) i b, ‖f n-g n‖ < δ/4 := by
    intro n hn
    have hN0 := balanced_complex_residue_cell_original_range N K (M*q) hK i b n hn
    have hCong := balanced_complex_residue_cell_congruent N K (M*q) i b a n ha hn
    have hRes := (native_rational_polynomial_integer_modEq_coset D j M q a n z y hM hCong hpow).trans hResidueA
    have hx : |(n : ℝ)| ≤ (N : ℝ) := by
      rw [abs_of_nonneg (by exact_mod_cast hN0.1)]
      exact_mod_cast hN0.2.le
    have hb : |(a : ℝ)| ≤ (N : ℝ) := by
      rw [abs_of_nonneg (by exact_mod_cast hA0.1)]
      exact_mod_cast hA0.2.le
    have hClose : |(n : ℝ)-(a : ℝ)| ≤ r*(N : ℝ) :=
      (balanced_complex_residue_cell_close N K (M*q) hK hTwo i b a n ha hn).trans (by
        have hh := mul_le_mul_of_nonneg_right hRadius (Nat.cast_nonneg N)
        simpa only [div_mul_eq_mul_div,mul_comm (N : ℝ)] using hh)
    exact hFreeze E M N hED h0 h1 hM hN hBounds F hF (n : ℝ) (a : ℝ) hx hb hClose
      _ _ _ ρ (hExact (n : ℝ)) hRes
  refine ⟨i,b,a,m,ha,Finset.mem_range.mp hm,hLength,hError,?_,?_⟩
  · exact native_conjugate_fourier_observable_zero_mean D L k ρ _ hk F
  · exact finite_complex_frozen_mean_large _ f g δ hδ (hSignal.trans hMean) (fun n hn => (hError n hn).le)

end Hindman168
