import Hindman168.NativeRationalErrorFourierFreezing
import Hindman168.NativeConjugateFourierObservable

/-! TRUE right-ordered original group sample / original lattice residue
plus REAL error coefficients yield genuine complex approximation by the
ACTUAL frozen observable on TRUE conjugated native data. -/
namespace Hindman168
open Polynomial
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_right_sample_freezing {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (y : D.E) (j : ℕ) (A ε : ℝ)
    (hA : 0 ≤ A) (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ (E : ℝ[X]) (M N : ℕ),
      E.natDegree ≤ j → E.coeff 0=0 → E.coeff 1=0 → 0 < M → 0 < N →
      (∀ i : ℕ, 2 ≤ i → i ≤ j → (M : ℝ)*(N : ℝ)^i*|E.coeff i| ≤ A) →
      ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ), ∀ (x b : ℝ),
        |x| ≤ (N : ℝ) → |b| ≤ (N : ℝ) → |x-b| ≤ r*(N : ℝ) →
        ∀ (g h γ ρ : D.G),
          g=nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval x • y)*h*γ →
          (γ : D.G ⧸ D.Γ)=(ρ : D.G ⧸ D.Γ) →
          (letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric;
           letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
             (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace;
           ‖nativeRationalTerminalFourierProjection D L k F (g : D.G ⧸ D.Γ)-
             nativeConjugateFourierObservable D L k ρ
               (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval b • y)) F
                 (h : D.G ⧸ roughConjugateSubgroup D.Γ ρ)‖ < ε) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨r,hr,hr1,hFreeze⟩ := native_rational_error_fourier_freezing D L k y j A ε hA hε
  refine ⟨r,hr,hr1,?_⟩
  intro E M N hD h0 h1 hM hN hBound F hF x b hx hb hxb g h γ ρ hExact hResidue
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
    (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
  have hCoset : (g : D.G ⧸ D.Γ)=
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval x • y)*h*ρ : D.G ⧸ D.Γ) := by
    rw [hExact]
    exact congrArg (fun q : D.G ⧸ D.Γ =>
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval x • y)*h) • q) hResidue
  rw [hCoset,native_conjugate_fourier_observable_sample]
  have hh := hFreeze E M N hD h0 h1 hM hN hBound F hF x b (h*ρ : D.G ⧸ D.Γ) hx hb hxb
  change ‖nativeRationalTerminalFourierProjection D L k F
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval x • y)*(h*ρ) : D.G ⧸ D.Γ)-
      nativeRationalTerminalFourierProjection D L k F
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval b • y)*(h*ρ) : D.G ⧸ D.Γ)‖ < ε at hh
  simpa only [mul_assoc] using hh

end Hindman168
