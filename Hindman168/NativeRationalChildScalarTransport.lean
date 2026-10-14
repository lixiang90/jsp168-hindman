import Hindman168.NativeRationalConstructedChildSignal
import Hindman168.NativeConjugateHorizontalCharacter
import Hindman168.RoughVectorSpatialAffineProjection
import Hindman168.ScalarUnitPolynomial

/-! Exact ORIGINAL horizontal scalar identities from actual ALL-real group
factorization and literal child affine construction. Positive lattice powers
clear the rational factor coefficient by coefficient. No child inverse or
coefficient bound is supplied as an assumption standing in for induction. -/
namespace Hindman168
open Polynomial
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_right_factor_scalar_identity {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (κ : D.E →L[ℝ] ℝ)
    (hκ : RoughNativeHorizontalFunctional (I := D.I) D.Γ κ.toLinearMap)
    (p pK : RoughVectorMvPolynomial Unit D.E) (y : D.E) (E R : ℝ[X])
    (hExact : ∀ x : ℝ,
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) p (fun _ => x)) =
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval x • y) *
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) pK (fun _ => x)) *
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (R.eval x • y)) :
    scalarUnitPolynomial (roughVectorMvProjection κ.toLinearMap p) =
      scalarUnitPolynomial (roughVectorMvProjection κ.toLinearMap pK) +
        C (κ y) * E + C (κ y) * R := by
  apply Polynomial.funext
  intro x
  have h := congrArg (nativeLieLogarithmCharacter (I := D.I) (G := D.G) κ.toLinearMap) (hExact x)
  simp only [nativeLieLogarithmCharacter_mul κ.toLinearMap hκ.2.1,
    nativeLieLogarithmCharacter_exponential, map_smul, smul_eq_mul] at h
  change κ (roughVectorMvEval (E := D.E) p (fun _ => x)) =
    E.eval x * κ y + κ (roughVectorMvEval (E := D.E) pK (fun _ => x)) + R.eval x * κ y at h
  rw [scalar_unit_polynomial_eval, roughVectorMvProjection_eval,
    eval_add, eval_add, eval_mul, eval_mul, eval_C,
    scalar_unit_polynomial_eval, roughVectorMvProjection_eval]
  change κ (roughVectorMvEval (E := D.E) p (fun _ => x)) =
    κ (roughVectorMvEval (E := D.E) pK (fun _ => x)) + κ y * E.eval x + κ y * R.eval x
  rw [h]
  ring

theorem native_rational_progression_scalar_identity {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (κ : D.E →ₗ[ℝ] ℝ)
    (pK : RoughVectorMvPolynomial Unit D.E) (a : ℤ) (P : ℕ) :
    scalarUnitPolynomial (roughVectorMvProjection κ (nativeRationalProgressionPolynomial D pK a P)) =
      (scalarUnitPolynomial (roughVectorMvProjection κ pK)).comp (C (a : ℝ) + C (P : ℝ) * X) := by
  apply Polynomial.funext
  intro x
  rw [scalar_unit_polynomial_eval, roughVectorMvProjection_eval,
    nativeRationalProgressionPolynomial, roughVectorMvAffineSubstitution_eval,
    eval_comp, eval_add, eval_mul, eval_C, eval_C, eval_X,
    scalar_unit_polynomial_eval, roughVectorMvProjection_eval]

theorem native_rational_horizontal_positive_power_integer {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (κ : D.E →ₗ[ℝ] ℝ)
    (hκ : RoughNativeHorizontalFunctional (I := D.I) D.Γ κ)
    (y : D.E) (q : ℕ)
    (hpow : nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ) :
    ∃ z : ℤ, (q : ℝ) * κ y = (z : ℝ) := by
  obtain ⟨z,hz⟩ := hκ.2.2 _ hpow
  rw [← nativeLieExponential_nat_smul (E := D.E) (I := D.I) (G := D.G) y q,
    nativeLieGlobalLogarithm_exponential, map_smul] at hz
  exact ⟨z,hz⟩

theorem native_rational_horizontal_rational_coeff_integer {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (κ : D.E →ₗ[ℝ] ℝ)
    (hκ : RoughNativeHorizontalFunctional (I := D.I) D.Γ κ)
    (y : D.E) (q M d : ℕ) (hM : 0 < M) (z : ℕ → ℤ)
    (hpow : nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ)
    (i : ℕ) :
    ∃ w : ℤ, ((M*q : ℕ) : ℝ) * (C (κ y) * scalarNonlinearRationalPart d M z).coeff i = (w : ℝ) := by
  obtain ⟨b,hb⟩ := native_rational_horizontal_positive_power_integer D κ hκ y q hpow
  rw [coeff_C_mul, scalar_nonlinear_rational_part_coeff]
  split_ifs with hi
  · refine ⟨b*z i,?_⟩
    have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [Nat.cast_mul, Int.cast_mul]
    field_simp
    rw [hb]
    ring
  · exact ⟨0,by simp⟩

end Hindman168
