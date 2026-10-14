import Hindman168.NativeRationalOriginalCoefficientTransport

/-! One fixed ORIGINAL character/grid and BOTH-table budget precedes ALL
bounded rational multipliers, child characters and raw sources. The actual
coefficient transport input is explicit; no child inverse is claimed. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u

noncomputable def nativeRationalUniformOriginalTransportBound (d S B : ℕ) (AK AE C : ℝ) : ℝ :=
  ((S*B : ℕ) : ℝ)*
    (((roughSpatialDegreeIndices Unit d).card : ℝ)*(2 : ℝ)^d*
      (((S*B)^d : ℕ) : ℝ)*AK*(B : ℝ)^d)+
    (((S*B)^d : ℕ) : ℝ)*(B : ℝ)*(C*(B : ℝ))*AE

theorem native_rational_original_transport_budget_uniform (d M q S B : ℕ) (AK AE C c : ℝ)
    (hM : M ≤ S) (hq : q ≤ B) (hAK : 0 ≤ AK) (hAE : 0 ≤ AE) (_hC : 0 ≤ C)
    (hc : |c| ≤ C*(B : ℝ)) :
    nativeRationalOriginalTransportBudget d M q B AK AE c ≤
      nativeRationalUniformOriginalTransportBound d S B AK AE C := by
  have hPeriod : ((M*q : ℕ) : ℝ) ≤ ((S*B : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul hM hq
  have hqR : (q : ℝ) ≤ (B : ℝ) := by exact_mod_cast hq
  unfold nativeRationalOriginalTransportBudget nativeRationalUniformOriginalTransportBound
  simp only [Nat.cast_pow]
  gcongr

theorem native_rational_uniform_original_transport_character {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d S B : ℕ) (AK AE C : ℝ)
    (hAK : 0 ≤ AK) (hAE : 0 ≤ AE) (hC : 0 ≤ C) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ (M q : ℕ), 0 < M → M ≤ S → 0 < q → q ≤ B →
      ∀ (κ : D.E →L[ℝ] ℝ), RoughNativeHorizontalFunctional (I := D.I) D.Γ κ.toLinearMap → ‖κ‖ ≤ C →
      ∀ y : D.E, ‖y‖ ≤ (B : ℝ) → ∀ (p : RoughVectorMvPolynomial Unit D.E) (N : ℕ), 0 < N →
      (∀ I : Unit → ℕ, 0 < (∑ i, I i) →
        (N : ℝ)^(∑ i, I i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
          (roughVectorMvProjection ((((M*q)^(d+1) : ℕ) : ℝ) • κ.toLinearMap) p) : ℝ) : UnitAddCircle)‖ ≤
          nativeRationalOriginalTransportBudget d M q B AK AE (κ y)) →
      ∃ χ : D.E →L[ℝ] ℝ,
        RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧ ‖χ‖ ≤ (Q : ℝ) ∧
        χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (Q : ℝ) ∧
        (∀ I : Unit → ℕ, 0 < (∑ i, I i) →
          (N : ℝ)^(∑ i, I i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
            (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)) ∧
        ∀ I : Unit → ℕ, 0 < (∑ i, I i) →
          (N : ℝ)^(∑ i, I i)*‖((mvPolynomialBinomialCoefficient
            (roughVectorMvProjection χ.toLinearMap p) d I : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ) := by
  let A := nativeRationalUniformOriginalTransportBound d S B AK AE C
  let R := (((S*B)^(d+1) : ℕ) : ℝ)*C
  let V := (mvBinomialCoefficientBudget Unit d : ℝ)*A
  have hA : 0 ≤ A := by dsimp only [A,nativeRationalUniformOriginalTransportBound]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  let Q := 1+⌈R+A+V⌉₊
  have hQ : 0 < Q := by dsimp only [Q]; omega
  have hSumQ : R+A+V ≤ (Q : ℝ) := (Nat.le_ceil _).trans (by dsimp only [Q]; push_cast; linarith)
  have hAQ : A ≤ (Q : ℝ) := by linarith only [hSumQ,hR,hV]
  have hRQ : R ≤ (Q : ℝ) := by linarith only [hSumQ,hA,hV]
  have hVQ : V ≤ (Q : ℝ) := by linarith only [hSumQ,hR,hA]
  refine ⟨Q,hQ,?_⟩
  intro M q hM hMS hq hqB κ hHor hκ y hy p N hN hMono
  let U := (M*q)^(d+1)
  let χ := (U : ℝ) • κ
  have hU : 0 < U := Nat.pow_pos (Nat.mul_pos hM hq)
  have hUR : (U : ℝ) ≤ (((S*B)^(d+1) : ℕ) : ℝ) := by
    dsimp only [U]
    exact_mod_cast Nat.pow_le_pow_left (Nat.mul_le_mul hMS hqB) (d+1)
  have hc : |κ y| ≤ C*(B : ℝ) := by
    have h := κ.le_opNorm y
    rw [Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul hκ hy (norm_nonneg _) hC)
  have hBudget : nativeRationalOriginalTransportBudget d M q B AK AE (κ y) ≤ A :=
    native_rational_original_transport_budget_uniform d M q S B AK AE C (κ y) hMS hqB hAK hAE hC hc
  have hHorNew : RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap :=
    native_horizontal_positive_natural_multiple D κ.toLinearMap hHor U hU
  have hNorm : ‖χ‖ ≤ (Q : ℝ) := by
    rw [native_horizontal_natural_multiple_norm D κ U]
    exact (mul_le_mul hUR hκ (norm_nonneg _) (by positivity)).trans hRQ
  have hMonoQ (I : Unit → ℕ) (hI : 0 < ∑ i, I i) :
      (N : ℝ)^(∑ i, I i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
        (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ A :=
    (hMono I hI).trans hBudget
  refine ⟨χ,hHorNew,hNorm,
    rough_native_norm_bounded_horizontal_grid_mem D.Γ (Q : ℝ) (Nat.cast_nonneg Q) χ hNorm hHorNew,
    fun I hI => (hMonoQ I hI).trans hAQ,?_⟩
  intro I hI
  exact (mv_complete_binomial_transfer _ d N A hN hA hMonoQ I hI).trans hVQ

end Hindman168
