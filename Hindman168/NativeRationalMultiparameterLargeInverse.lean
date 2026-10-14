import Hindman168.NativeRationalDenseDirectionReconstruction
import Hindman168.NaturalDivisionLengthBounds

/-! Corrected equal-cube native multiparameter inverse for ALL large N.
Actual native short lines produce a SAME finite original character; proved
scalar basepoint recovery, genuine multiplier thinning and simultaneous
directional reconstruction give BOTH raw ORIGINAL coefficient tables.
Every budget/threshold precedes raw coefficients, N and observables. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_rational_multiparameter_large_inverse {s ℓ n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hℓ : 1 ≤ ℓ)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ R N0 : ℕ, 0 < R ∧ 0 < N0 ∧
      ∀ p : RoughVectorMvPolynomial (Fin n) D.E, RoughVectorMvWeightedDegree L.layer p 0 →
      ∀ N : ℕ, N0 ≤ N → ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
      δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube (Fin n) N)
        (nativeMvPolynomialOrbit D p) F‖ →
      ∃ χ : D.E →L[ℝ] ℝ,
        RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧ ‖χ‖ ≤ (R : ℝ) ∧
        χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (R : ℝ) ∧
        (∀ I : Fin n → ℕ, 0 < (∑ j, I j) →
          (N : ℝ)^(∑ j, I j)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
            (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (R : ℝ)) ∧
        ∀ I : Fin n → ℕ, 0 < (∑ j, I j) →
          (N : ℝ)^(∑ j, I j)*‖((mvPolynomialBinomialCoefficient
            (roughVectorMvProjection χ.toLinearMap p) ℓ I : ℝ) : UnitAddCircle)‖ ≤ (R : ℝ) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨Q,hQ,hCommon⟩ := native_rational_common_line_character (n := n) D L δ hδ
  let A := nativeRationalLineCharacterPool D Q
  by_cases hA : A.Nonempty
  · have hAc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    have hAc1 : (1 : ℝ) ≤ A.card := by exact_mod_cast hA.card_pos
    let μ := (δ/2)/(8*(A.card : ℝ))
    have hμ : 0 < μ := by dsimp only [μ]; positivity
    have hμ1 : μ ≤ 1 := by
      dsimp only [μ]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8*(A.card : ℝ))).mpr
      nlinarith only [hδ1,hAc1]
    obtain ⟨B,hB,hForK⟩ := native_rational_dense_direction_reconstruction (n := n) D L hℓ μ hμ hμ1
    let V := B^(ℓ+1)
    let d := ℓ*V
    obtain ⟨K,hKR⟩ := exists_nat_gt ((16*((n : ℝ)+(d : ℝ)*(A.card : ℝ)+1))/δ)
    have hK : 0 < K := by exact_mod_cast lt_of_le_of_lt (by positivity : 0 ≤
      (16*((n : ℝ)+(d : ℝ)*(A.card : ℝ)+1))/δ) hKR
    have hScale : 16*((n : ℝ)+(d : ℝ)*(A.card : ℝ)+1) < δ*(K : ℝ) := by
      simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hKR
    have hSize : 8*(n : ℝ) ≤ (δ/2)*(K : ℝ) := by
      nlinarith only [hScale,(Nat.cast_nonneg n : (0 : ℝ) ≤ n),show (0 : ℝ) ≤ (d : ℝ)*(A.card : ℝ) by positivity]
    have hDir : 8*(d : ℝ)*(A.card : ℝ) < (δ/2)*(K : ℝ) := by
      nlinarith only [hScale,(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    obtain ⟨C,hC,hReconstruct⟩ := hForK K hK
    let τ := (((2*K^2 : ℕ) : ℝ))⁻¹
    have hτ : 0 < τ := by dsimp only [τ]; positivity
    have hτ1 : τ ≤ 1 := by
      dsimp only [τ]
      exact (inv_le_one₀ (by positivity)).mpr (by exact_mod_cast
        (Nat.mul_pos (by omega : 0 < 2) (Nat.pow_pos hK) : 0 < 2*K^2))
    let U := C*V*Q*(2*K^2)^ℓ
    let R := C*V*Q+U+mvBinomialCoefficientBudget (Fin n) ℓ*U+1
    let Hmin := 1+⌈10*(Q : ℝ)/μ⌉₊
    let N0 := B+K^2*Hmin+K^2+1
    have hR : 0 < R := by dsimp only [R]; omega
    have hN0 : 0 < N0 := by dsimp only [N0]; omega
    have hNormCap : ((C*V*Q : ℕ) : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast (show C*V*Q ≤ R by dsimp only [R]; omega)
    have hMonoCap : (C : ℝ)*((B^(ℓ+1) : ℕ) : ℝ)*(Q : ℝ)*(τ⁻¹)^ℓ ≤ (R : ℝ) := by
      dsimp only [τ]
      rw [inv_inv]
      exact_mod_cast (show C*B^(ℓ+1)*Q*(2*K^2)^ℓ ≤ R by dsimp only [R,U,V]; omega)
    have hBinCap : (mvBinomialCoefficientBudget (Fin n) ℓ : ℝ)*
        ((C : ℝ)*((B^(ℓ+1) : ℕ) : ℝ)*(Q : ℝ)*(τ⁻¹)^ℓ) ≤ (R : ℝ) := by
      dsimp only [τ]
      rw [inv_inv]
      exact_mod_cast (show mvBinomialCoefficientBudget (Fin n) ℓ*(C*B^(ℓ+1)*Q*(2*K^2)^ℓ) ≤ R by
        dsimp only [R,U,V]; omega)
    refine ⟨R,N0,hR,hN0,?_⟩
    intro p hp N hN0N F hF hBad
    have hBN : B ≤ N := (show B ≤ N0 by dsimp only [N0]; omega).trans hN0N
    have hKN : K^2 ≤ N := (show K^2 ≤ N0 by dsimp only [N0]; omega).trans hN0N
    have hMin : Hmin ≤ N/K^2 := (Nat.le_div_iff_mul_le (by positivity)).mpr (by
      have h := (show K^2*Hmin ≤ N0 by dsimp only [N0]; omega).trans hN0N
      simpa only [Nat.mul_comm] using h)
    have hH : 0 < N/K^2 := Nat.div_pos hKN (by positivity)
    have hHReal : (0 : ℝ) < (N/K^2 : ℕ) := by exact_mod_cast hH
    have hMinReal : 10*(Q : ℝ)/μ ≤ (N/K^2 : ℕ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈10*(Q : ℝ)/μ⌉₊ ≤ Hmin by dsimp only [Hmin]; omega).trans hMin)
    have hTol : (Q : ℝ)/(N/K^2 : ℕ) ≤ μ/10 := by
      have h := (div_le_iff₀ hμ).mp hMinReal
      apply (div_le_iff₀ hHReal).mpr
      nlinarith only [h]
    have hLength : τ*(N : ℝ) ≤ (N/K^2 : ℕ) := by
      simpa only [τ,div_eq_mul_inv,mul_comm] using natural_division_length_lower N (K^2) (by positivity) hKN
    obtain ⟨χ,hχ,S,hS,hDense,hRows⟩ := hCommon N K d hK hKN hSize hDir p hp F hF hBad
    obtain ⟨hHor,hNorm⟩ := native_rational_line_character_pool_properties D Q χ hχ
    obtain ⟨M,mult,_hM,_hMV,_hMult,_hMultC,hHorNew,hNormNew,_hGridNew,hMono,hBin⟩ :=
      hReconstruct p hp χ hHor Q N (N/K^2) τ hNorm hBN hH hTol hτ hτ1 hLength S hS hDense hRows
    let γ := ((mult*M : ℕ) : ℝ) • χ
    have hn : ‖γ‖ ≤ (R : ℝ) := hNormNew.trans hNormCap
    exact ⟨γ,hHorNew,hn,
      rough_native_norm_bounded_horizontal_grid_mem D.Γ (R : ℝ) (Nat.cast_nonneg R) γ hn hHorNew,
      fun I hI => (hMono I hI).trans hMonoCap,fun I hI => (hBin I hI).trans hBinCap⟩
  · obtain ⟨K,hKR⟩ := exists_nat_gt ((16*(n : ℝ))/δ)
    have hK : 0 < K := by exact_mod_cast lt_of_le_of_lt (by positivity : 0 ≤ (16*(n : ℝ))/δ) hKR
    have hScale : 16*(n : ℝ) < δ*(K : ℝ) := by
      simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hKR
    have hSize : 8*(n : ℝ) ≤ (δ/2)*(K : ℝ) := by nlinarith only [hScale]
    have hDir : 8*((0 : ℕ) : ℝ)*((nativeRationalLineCharacterPool D Q).card : ℝ) < (δ/2)*(K : ℝ) := by
      simp only [Nat.cast_zero,mul_zero,zero_mul]
      positivity
    refine ⟨1,K^2,by omega,by positivity,?_⟩
    intro p hp N hKN F hF hBad
    obtain ⟨χ,hχ,_T,_hT,_hDense,_hRows⟩ := hCommon N K 0 hK hKN hSize hDir p hp F hF hBad
    exact (hA ⟨χ,hχ⟩).elim

end Hindman168
