import Hindman168.NativeRationalFourierScalarFreezing
import Hindman168.ScalarNonlinearSmallVariation

/-! REAL original-scale error coefficients give actual COMPLEX Fourier
freezing on a true fixed fractional short interval. Radius precedes every
error polynomial/M/N/sample; total error value is only bounded. -/
namespace Hindman168
open Polynomial
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_error_fourier_freezing {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (y : D.E) (j : ℕ) (A ε : ℝ)
    (hA : 0 ≤ A) (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ (E : ℝ[X]) (M N : ℕ),
      E.natDegree ≤ j → E.coeff 0=0 → E.coeff 1=0 → 0 < M → 0 < N →
      (∀ i : ℕ, 2 ≤ i → i ≤ j → (M : ℝ)*(N : ℝ)^i*|E.coeff i| ≤ A) →
      ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        ∀ (x b : ℝ) (q : D.G ⧸ D.Γ), |x| ≤ (N : ℝ) → |b| ≤ (N : ℝ) →
          |x-b| ≤ r*(N : ℝ) →
            ‖nativeRationalTerminalFourierProjection D L k F
              (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval x • y) • q)-
                nativeRationalTerminalFourierProjection D L k F
                  (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval b • y) • q)‖ < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  let B := ((j+1 : ℕ) : ℝ)^2*A
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨η,hη,hFreeze⟩ := native_rational_fourier_scalar_freezing D L k y B ε hε
  let r := min 1 (η/(B+1))
  have hr : 0 < r := lt_min (by norm_num) (div_pos hη (by positivity))
  have hSmall : B*r ≤ η := by
    have hh := (le_div_iff₀ (by positivity : 0 < B+1)).mp (min_le_right 1 (η/(B+1)))
    change r*(B+1) ≤ η at hh
    nlinarith
  refine ⟨r,hr,min_le_left _ _,?_⟩
  intro E M N hDegree h0 h1 hM hN hBounds F hF x b q hx hb hxb
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hV := scalar_nonlinear_small_variation E j M N A hDegree h0 h1 hN hA hBounds
    x b (r*(N : ℝ)) (by positivity) hx hb hxb
  have he : r*(N : ℝ)/(N : ℝ)=r := by field_simp
  rw [he] at hV
  apply hFreeze F hF (E.eval x) (E.eval b) q
  · exact scalar_nonlinear_small_value_bound E j M N A hDegree h0 h1 hM hN hA hBounds x hx
  · exact scalar_nonlinear_small_value_bound E j M N A hDegree h0 h1 hM hN hA hBounds b hb
  · exact ((le_mul_of_one_le_left (abs_nonneg _) hm).trans hV).trans hSmall

end Hindman168
