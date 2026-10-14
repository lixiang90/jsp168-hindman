import Hindman168.NativeRationalChildScalarTransport
import Hindman168.RoughAffineCoefficientRecovery
import Hindman168.ScalarRightFactorCoefficientTransport
import Hindman168.NativeHorizontalNaturalMultiplier
import Hindman168.MvCompleteBinomialTransfer

/-! BOTH COMPLETE raw ORIGINAL coefficient tables are recovered from TRUE
constructed affine child coefficients, the ALL-real source factorization and
REAL error bounds. Child coefficients must be derived by future genuine IH;
this is a transport theorem, not an assumed inverse or the final inverse. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalOriginalTransportBudget (d M q B : ℕ) (AK AE c : ℝ) : ℝ :=
  ((M*q : ℕ) : ℝ)*
    (((roughSpatialDegreeIndices Unit d).card : ℝ)*(2 : ℝ)^d*
      (((M*q)^d : ℕ) : ℝ)*AK*(B : ℝ)^d)+
    (((M*q)^d : ℕ) : ℝ)*(q : ℝ)*|c| * AE

theorem native_rational_original_coefficient_transport {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (κ : D.E →L[ℝ] ℝ)
    (hκ : RoughNativeHorizontalFunctional (I := D.I) D.Γ κ.toLinearMap)
    (p pK pNew : RoughVectorMvPolynomial Unit D.E) (y : D.E)
    (d j M q B N T : ℕ) (a : ℤ) (z : ℕ → ℤ) (E : Polynomial ℝ) (AK AE : ℝ)
    (hM : 0 < M) (hq : 0 < q) (hB : 0 < B) (hN : 0 < N)
    (ha : 0 ≤ a) (haN : a < (N : ℤ)) (hAK : 0 ≤ AK) (hAE : 0 ≤ AE)
    (hLength : (N : ℝ)/(B : ℝ) ≤ T)
    (hDegree : RoughVectorMvDegreeLE pK d)
    (hConstructed : pNew=nativeRationalProgressionPolynomial D pK a (M*q))
    (hEDegree : E.natDegree ≤ j) (hEOne : E.coeff 1=0)
    (hError : ∀ i : ℕ, 2 ≤ i → i ≤ j → (M : ℝ)*(N : ℝ)^i*|E.coeff i| ≤ AE)
    (hPower : nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ)
    (hExact : ∀ x : ℝ,
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) p (fun _ => x)) =
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval x • y)*
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) pK (fun _ => x))*
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          ((scalarNonlinearRationalPart j M z).eval x • y))
    (hChild : ∀ I : Unit → ℕ, 0 < (∑ i, I i) →
      (T : ℝ)^(∑ i, I i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
        (roughVectorMvProjection κ.toLinearMap pNew) : ℝ) : UnitAddCircle)‖ ≤ AK) :
    let κNew := (((M*q)^(d+1) : ℕ) : ℝ) • κ
    let A := nativeRationalOriginalTransportBudget d M q B AK AE (κ y)
    (∀ I : Unit → ℕ, 0 < (∑ i, I i) →
      (N : ℝ)^(∑ i, I i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
        (roughVectorMvProjection κNew.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ A) ∧
    ∀ I : Unit → ℕ, 0 < (∑ i, I i) →
      (N : ℝ)^(∑ i, I i)*‖((mvPolynomialBinomialCoefficient
        (roughVectorMvProjection κNew.toLinearMap p) d I : ℝ) : UnitAddCircle)‖ ≤
      (mvBinomialCoefficientBudget Unit d : ℝ)*A := by
  let period := M*q
  let PK := roughVectorMvProjection κ.toLinearMap pK
  let AK0 := ((roughSpatialDegreeIndices Unit d).card : ℝ)*(2 : ℝ)^d*
      ((period^d : ℕ) : ℝ)*AK*(B : ℝ)^d
  have hPeriod : 0 < period := Nat.mul_pos hM hq
  have hB0 : 0 < (B : ℝ) := by exact_mod_cast hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hInv1 : (B : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hB0).mpr hB1
  have hChild' : ∀ I : Unit → ℕ, 0 < (∑ i, I i) →
      (T : ℝ)^(∑ i, I i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
        (roughMvAffineSubstitution (fun _ => (a : ℝ)) (fun _ => (period : ℝ)) PK) : ℝ) : UnitAddCircle)‖ ≤ AK := by
    intro I hI
    have h := hChild I hI
    rw [hConstructed,nativeRationalProgressionPolynomial,rough_vector_projection_affine_substitution] at h
    exact h
  have haReal : |(a : ℝ)| ≤ (N : ℝ) := by
    rw [abs_of_nonneg (by exact_mod_cast ha)]
    exact_mod_cast haN.le
  have hPK (I : Unit → ℕ) (hI : 0 < ∑ i, I i) :
      (N : ℝ)^(∑ i, I i)*‖((((period^d : ℕ) : ℝ)*
        MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) PK : ℝ) : UnitAddCircle)‖ ≤ AK0 := by
    have h := rough_affine_coefficient_recovery PK d period N T (fun _ => a)
      (B : ℝ)⁻¹ 1 AK (roughVectorMvProjection_degree κ.toLinearMap hDegree)
      hPeriod hN (inv_pos.mpr hB0) hInv1 (by norm_num) hAK
      (by simpa only [div_eq_mul_inv,mul_comm] using hLength)
      (fun _ => by simpa only [one_mul] using haReal) hChild' I hI
    simpa only [inv_inv,max_self,one_pow,mul_one,mul_assoc,AK0] using h
  have hScalar := native_rational_right_factor_scalar_identity D κ hκ p pK y E
    (scalarNonlinearRationalPart j M z) hExact
  have hE := scalar_nonlinear_error_all_positive_coefficients E j M N AE hAE hEDegree hEOne hError
  let κNew := (((M*q)^(d+1) : ℕ) : ℝ) • κ
  let A := nativeRationalOriginalTransportBudget d M q B AK AE (κ y)
  have hA : 0 ≤ A := by dsimp only [A,nativeRationalOriginalTransportBudget]; positivity
  have hMono (I : Unit → ℕ) (hI : 0 < ∑ i, I i) :
      (N : ℝ)^(∑ i, I i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
        (roughVectorMvProjection κNew.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ A := by
    have hSingle : Finsupp.equivFunOnFinite.symm I=Finsupp.single () (I ()) := by
      apply Finsupp.ext
      intro u
      cases u
      simp
    have hi : 0 < I () := by simpa only [Finset.univ_unique,Finset.sum_singleton] using hI
    have hk := hPK I hI
    rw [hSingle,← scalar_unit_polynomial_coefficient] at hk
    simp only [Finset.univ_unique,Finset.sum_singleton] at hk
    have h := scalar_right_factor_coefficient_transport
      (scalarUnitPolynomial (roughVectorMvProjection κ.toLinearMap p))
      (scalarUnitPolynomial PK) E (scalarNonlinearRationalPart j M z)
      (κ y) (period^d) M q N (I ()) AK0 AE hScalar
      (native_rational_horizontal_rational_coeff_integer D κ.toLinearMap hκ y q M j hM z hPower (I ()))
      hk (hE (I ()) hi)
    change (N : ℝ)^(∑ i, I i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
      (roughVectorMvProjection ((((M*q)^(d+1) : ℕ) : ℝ) • κ.toLinearMap) p) : ℝ) : UnitAddCircle)‖ ≤ A
    rw [rough_vector_projection_smul,MvPolynomial.coeff_C_mul,hSingle,
      ← scalar_unit_polynomial_coefficient]
    simpa only [Finset.univ_unique,Finset.sum_singleton,period,pow_succ,
      Nat.cast_mul,A,nativeRationalOriginalTransportBudget,AK0,mul_assoc] using h
  exact ⟨hMono,mv_complete_binomial_transfer _ d N A hN hA hMono⟩

end Hindman168
