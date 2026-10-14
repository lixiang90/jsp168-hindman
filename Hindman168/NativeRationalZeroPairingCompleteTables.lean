import Hindman168.NativeRationalZeroPairingAffineBracket
import Hindman168.ScalarQuadraticCoefficientCompletion

/-! SAME zero-pairing dense native bracket yields one ACTUAL positive
common natural multiplier with COMPLETE nonlinear tables, all higher
diagonal tables and P(1) bound. Constants precede every raw source/N. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_zero_pairing_complete_tables {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (δ B : ℝ) (S : ℕ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B) (hS : 0 < S) :
    ∃ A S' T : ℕ, 0 < A ∧ 0 < S' ∧ 0 < T ∧ ∀ (p : RoughVectorMvPolynomial Unit D.E)
      (hp : RoughVectorMvWeightedDegree L.layer p 0)
      (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ),
      (∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0) →
      ∀ M : ℕ, 0 < M → M ≤ S → ∀ N : ℕ, T ≤ N →
      (∀ j : ℕ, 3 ≤ j → j ≤ ℓ → (N : ℝ)^j*‖(((M : ℝ)*(nativeRationalCompactNonlinearScalar D L p hp χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ B) →
      (∀ j : ℕ, 2 ≤ j → j ≤ ℓ → (N : ℝ)^j*‖(((M : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ B) →
      (∀ j : ℕ, 2 ≤ j → j ≤ ℓ → (N : ℝ)^j*‖(((M : ℝ)*scalarPolynomialBinomialCoefficient (nativeRationalCompactDiagonalScalar D L p χ) ℓ j : ℝ) : UnitAddCircle)‖ ≤ B) →
      ∀ (b : NativeRationalFirstLayerIndex D L → ℤ) (V : Finset ℕ), δ*(N : ℝ) ≤ V.card →
      (∀ h ∈ V, h < N ∧ (N : ℝ)*‖((scalarFractionalBracket
        (nativeRationalCompactBracketBeta D L p χ M b) (nativeRationalCompactBracketAlpha D L p hp χ M)
        (nativeRationalCompactBracketCoefficient D L p χ M) (nativeRationalCompactBracketFrequency D L p)
        (h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ B) →
      ∃ M' : ℕ, 0 < M' ∧ M' ≤ S' ∧
        (∀ j : ℕ, 2 ≤ j → j ≤ ℓ → (N : ℝ)^j*‖(((M' : ℝ)*(nativeRationalCompactNonlinearScalar D L p hp χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
        (∀ j : ℕ, 2 ≤ j → j ≤ ℓ → (N : ℝ)^j*‖(((M' : ℝ)*scalarPolynomialBinomialCoefficient (nativeRationalCompactNonlinearScalar D L p hp χ) ℓ j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
        (∀ j : ℕ, 2 ≤ j → j ≤ ℓ → (N : ℝ)^j*‖(((M' : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
        (∀ j : ℕ, 2 ≤ j → j ≤ ℓ → (N : ℝ)^j*‖(((M' : ℝ)*scalarPolynomialBinomialCoefficient (nativeRationalCompactDiagonalScalar D L p χ) ℓ j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
        (N : ℝ)*‖(((M' : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).eval 1 : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  obtain ⟨R,T,hR,hT,hAffine⟩ := native_rational_zero_pairing_affine_inverse D L δ B hδ hδ1 hB
  let S' := 2*R*S
  let C := (1+(scalarBinomialCoefficientBudget ℓ : ℝ))*(2+(scalarBinomialCoefficientBudget ℓ : ℝ))*((R : ℝ)*B)
  let E := C+2*(R : ℝ)*B
  let A := ⌈E⌉₊+1
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have h2B : 0 ≤ 2*(R : ℝ)*B := by positivity
  have hEA : E ≤ (A : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ ⌈E⌉₊)
  have hCA : C ≤ (A : ℝ) := (show C ≤ E by dsimp only [E]; linarith).trans hEA
  have h2A : 2*(R : ℝ)*B ≤ (A : ℝ) := (show _ ≤ E by dsimp only [E]; linarith).trans hEA
  have hRaise (r K : ℕ) (t x b0 : ℝ) (ht : 0 ≤ t) (hb0 : 0 ≤ b0) (hr : r ≤ K)
      (hx : t*‖(x : UnitAddCircle)‖ ≤ b0) :
      t*‖(((r : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ (K : ℝ)*b0 := by
    calc
      _ ≤ t*((r : ℝ)*‖(x : UnitAddCircle)‖) := mul_le_mul_of_nonneg_left (mod_one_natural_multiplier_norm_le r x) ht
      _ = (r : ℝ)*(t*‖(x : UnitAddCircle)‖) := by ring
      _ ≤ (r : ℝ)*b0 := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg r)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hr) hb0
  refine ⟨A,S',T,by dsimp only [A]; omega,by dsimp only [S']; positivity,hT,?_⟩
  intro p hp χ hzero M hM hMS N hTN hQM hPM hPB b V hdense hUseful
  have hN : 0 < N := hT.trans_le hTN
  obtain ⟨r,hr,hrR,hSecond,hEval⟩ := hAffine p hp χ hzero M b N hTN V hdense hUseful
  have hHigher : ∀ j : ℕ, 3 ≤ j → j ≤ ℓ →
      (N : ℝ)^j*‖((((r*M : ℕ) : ℝ)*(nativeRationalCompactNonlinearScalar D L p hp χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ (R : ℝ)*B := by
    intro j hj hjL
    have hh := hRaise r R ((N : ℝ)^j) ((M : ℝ)*(nativeRationalCompactNonlinearScalar D L p hp χ).coeff j)
      B (pow_nonneg (Nat.cast_nonneg N) j) hB hrR (hQM j hj hjL)
    simpa only [Nat.cast_mul,mul_assoc] using hh
  obtain ⟨hQMono,hQBin⟩ := scalar_quadratic_complete_tables
    (nativeRationalCompactNonlinearScalar D L p hp χ) ℓ (r*M) N ((R : ℝ)*B) hdeg hN (by positivity) hSecond hHigher
  let M' := 2*(r*M)
  have hM' : 0 < M' := Nat.mul_pos (by omega) (Nat.mul_pos hr hM)
  have hMS' : M' ≤ S' := by
    have hh := Nat.mul_le_mul hrR hMS
    simpa only [M',S',Nat.mul_assoc] using Nat.mul_le_mul_left 2 hh
  have hIdentity (x : ℝ) : (M' : ℝ)*x = ((2*r : ℕ) : ℝ)*((M : ℝ)*x) := by dsimp only [M']; push_cast; ring
  have hPMono : ∀ j : ℕ, 2 ≤ j → j ≤ ℓ →
      (N : ℝ)^j*‖(((M' : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
    intro j hj hjL
    rw [hIdentity]
    have hh := hRaise (2*r) (2*R) ((N : ℝ)^j) ((M : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).coeff j)
      B (pow_nonneg (Nat.cast_nonneg N) j) hB (Nat.mul_le_mul_left 2 hrR) (hPM j hj hjL)
    exact hh.trans (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using h2A)
  have hPBin : ∀ j : ℕ, 2 ≤ j → j ≤ ℓ →
      (N : ℝ)^j*‖(((M' : ℝ)*scalarPolynomialBinomialCoefficient (nativeRationalCompactDiagonalScalar D L p χ) ℓ j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
    intro j hj hjL
    rw [hIdentity]
    have hh := hRaise (2*r) (2*R) ((N : ℝ)^j) ((M : ℝ)*scalarPolynomialBinomialCoefficient (nativeRationalCompactDiagonalScalar D L p χ) ℓ j)
      B (pow_nonneg (Nat.cast_nonneg N) j) hB (Nat.mul_le_mul_left 2 hrR) (hPB j hj hjL)
    exact hh.trans (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using h2A)
  have hEval' : (N : ℝ)*‖(((M' : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).eval 1 : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
    have he : (M' : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).eval 1 =
        (2 : ℝ)*(((r*M : ℕ) : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).eval 1) := by dsimp only [M']; push_cast; ring
    rw [he]
    have hh := hRaise 2 2 (N : ℝ) (((r*M : ℕ) : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).eval 1)
      ((R : ℝ)*B) (Nat.cast_nonneg N) (by positivity) le_rfl hEval
    norm_num only [Nat.cast_ofNat] at hh
    exact hh.trans (by nlinarith [h2A])
  exact ⟨M',hM',hMS',fun j hj hjL => (hQMono j hj hjL).trans hCA,
    fun j hj hjL => (hQBin j hj hjL).trans hCA,hPMono,hPBin,hEval'⟩

end Hindman168
