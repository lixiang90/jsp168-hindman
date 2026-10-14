import Hindman168.NativeRationalLineConstantRecovery
import Hindman168.FiniteDirectionLabelThinning
import Hindman168.LeibmanCompleteDirectionalCoefficients
import Hindman168.NativeHorizontalNaturalMultiplier
import Hindman168.MvCompleteBinomialTransfer

/-! TRUE dense native line rows now return ONE SAME original nonzero
character with BOTH COMPLETE original tables. A proved scalar inverse,
exact positive multiplier thinning and all-degree integer reconstruction
are composed. B precedes K; all budgets precede raw source/character/N. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_rational_dense_direction_reconstruction {s ℓ n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hℓ : 1 ≤ ℓ)
    (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    ∃ B : ℕ, 0 < B ∧ ∀ K : ℕ, 0 < K → ∃ C : ℕ, 0 < C ∧
      ∀ (p : RoughVectorMvPolynomial (Fin n) D.E), RoughVectorMvWeightedDegree L.layer p 0 →
      ∀ (χ : D.E →L[ℝ] ℝ), RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap →
      ∀ (Q N H : ℕ) (τ : ℝ), ‖χ‖ ≤ (Q : ℝ) → B ≤ N → 0 < H →
      (Q : ℝ)/(H : ℝ) ≤ μ/10 → 0 < τ → τ ≤ 1 → τ*(N : ℝ) ≤ H →
      ∀ S : Finset (Fin n → ℕ), S ⊆ Fintype.piFinset (fun _ : Fin n => Finset.range K) →
      (ℓ*B^(ℓ+1))*K^n < S.card*K →
      (∀ q ∈ S, μ*((scalarMvIntegerCube (Fin n) N).card : ℝ) ≤
        (((scalarMvIntegerCube (Fin n) N).filter (NativeRationalLineBounds D p ℓ Q H χ q)).card : ℝ)) →
      ∃ M mult : ℕ, 0 < M ∧ M ≤ B^(ℓ+1) ∧ 0 < mult ∧ mult ≤ C ∧
        let γ := ((mult*M : ℕ) : ℝ) • χ
        let A := (C : ℝ)*((B^(ℓ+1) : ℕ) : ℝ)*(Q : ℝ)*(τ⁻¹)^ℓ
        RoughNativeHorizontalFunctional (I := D.I) D.Γ γ.toLinearMap ∧
        ‖γ‖ ≤ ((C*B^(ℓ+1)*Q : ℕ) : ℝ) ∧
        γ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ ((C*B^(ℓ+1)*Q : ℕ) : ℝ) ∧
        (∀ I : Fin n → ℕ, 0 < (∑ j, I j) →
          (N : ℝ)^(∑ j, I j)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
            (roughVectorMvProjection γ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ A) ∧
        ∀ I : Fin n → ℕ, 0 < (∑ j, I j) →
          (N : ℝ)^(∑ j, I j)*‖((mvPolynomialBinomialCoefficient
            (roughVectorMvProjection γ.toLinearMap p) ℓ I : ℝ) : UnitAddCircle)‖ ≤
            (mvBinomialCoefficientBudget (Fin n) ℓ : ℝ)*A := by
  obtain ⟨B,hB,hRecovery⟩ := native_rational_line_constant_recovery D L hℓ μ hμ hμ1
  refine ⟨B,hB,?_⟩
  intro K hK
  obtain ⟨C,hC,hReconstruct⟩ := leibman_complete_directional_coefficients n ℓ K hK
  refine ⟨C,hC,?_⟩
  intro p hp χ hHor Q N H τ hNorm hBN hH hTol hτ hτ1 hLength S hS hDense hRows
  let V := B^(ℓ+1)
  let P (M : ℕ) (q : Fin n → ℕ) := ∀ r : ℕ, 0 < r → r ≤ ℓ →
    ‖(((M : ℝ)*MvPolynomial.coeff 0 (scalarMvLineCoefficient
      (roughVectorMvProjection χ.toLinearMap p) (fun j => (q j : ℝ)) r) : ℝ) : UnitAddCircle)‖ ≤
      (V : ℝ)*((Q : ℝ)/(H : ℝ)^r)
  have hProduce (q : Fin n → ℕ) (hq : q ∈ S) : ∃ M : ℕ, 0 < M ∧ M ≤ V ∧ P M q :=
    hRecovery p hp χ q N H Q hBN hH hTol (hRows q hq)
  obtain ⟨M,hM,hMV,T,hTS,hTDense,hLabels⟩ := finite_dense_direction_label_thinning S ℓ V K n
    (by dsimp only [V]; positivity) hDense P hProduce
  obtain ⟨mult,hMult,hMultC,hCoeff⟩ := hReconstruct T (hTS.trans hS) hTDense
  have hDegree := native_rational_functional_scalar_degree D L p hp χ ℓ
    (by rw [L.terminal]; exact bot_le)
  have hMonoRaw := hCoeff (roughVectorMvProjection χ.toLinearMap p) hDegree M N H
    ((V : ℝ)*(Q : ℝ)) τ hH (by positivity) hτ hτ1 hLength (by
      intro q hq r hr hrL
      simpa only [mul_div_assoc] using hLabels q hq r hr hrL)
  let γ := ((mult*M : ℕ) : ℝ) • χ
  let A := (C : ℝ)*(V : ℝ)*(Q : ℝ)*(τ⁻¹)^ℓ
  have hMono (I : Fin n → ℕ) (hI : 0 < ∑ j, I j) :
      (N : ℝ)^(∑ j, I j)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
        (roughVectorMvProjection γ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ A := by
    change (N : ℝ)^(∑ j, I j)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
      (roughVectorMvProjection (((mult*M : ℕ) : ℝ) • χ.toLinearMap) p) : ℝ) : UnitAddCircle)‖ ≤ A
    rw [rough_vector_projection_smul,MvPolynomial.coeff_C_mul]
    simpa only [A,mul_assoc] using hMonoRaw I hI
  have hHorγ : RoughNativeHorizontalFunctional (I := D.I) D.Γ γ.toLinearMap :=
    native_horizontal_positive_natural_multiple D χ.toLinearMap hHor (mult*M) (Nat.mul_pos hMult hM)
  have hScale : ((mult*M : ℕ) : ℝ) ≤ ((C*V : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul hMultC hMV
  have hNormγ : ‖γ‖ ≤ ((C*V*Q : ℕ) : ℝ) := by
    rw [native_horizontal_natural_multiple_norm D χ (mult*M)]
    have h := mul_le_mul hScale hNorm (norm_nonneg _) (Nat.cast_nonneg (C*V))
    simpa only [Nat.cast_mul] using h
  have hN : 0 < N := hB.trans_le hBN
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  exact ⟨M,mult,hM,hMV,hMult,hMultC,hHorγ,hNormγ,
    rough_native_norm_bounded_horizontal_grid_mem D.Γ ((C*V*Q : ℕ) : ℝ) (Nat.cast_nonneg _) γ hNormγ hHorγ,
    hMono,mv_complete_binomial_transfer _ ℓ N A hN hA hMono⟩

end Hindman168
