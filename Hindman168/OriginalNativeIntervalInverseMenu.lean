import Hindman168.NativePeriodicIntervalInverseThreshold
import Hindman168.OriginalBoundedNativeModelsLinearMenu

/-!
Uncompiled conditional bridge, separated from the upstream inverse endpoint.

This module uses only the existing bounded rational-model menu and same-step
linearization. It introduces no inverse existence assertion as an axiom.
The hypothesis below is supplied separately by the fixed OpenAI inverse
theorem in `work-in-progress/OriginalNativeIntervalAdapter.lean`.
-/

namespace Hindman168
open OAI.Erdos3 OriginalBoundedNativeModels
open scoped BigOperators Classical NNReal Topology

/-- The exact rational niltest input consumed by the native finite menu.
The complexity and correlation bounds precede the period, interval, and input.
The correlation uses the upstream conjugation convention. -/
def HasUniformOriginalIntervalNiltestInverse (s d : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ p : ℝ, 0 ≤ p ∧ ∃ γ : ℝ, 0 < γ ∧
    ∀ (q : ℕ) [NeZero q] (K : ℕ) (v : ZMod q → ℝ),
      (∀ z, |v z| ≤ 1) →
      δ / 4 ≤ integerIntervalPeriodicGowersValue q d (K * q) v →
      ∃ A : RationalGeometry s, ∃ T : A.model.Niltest (fun _ : Unit => 1),
        T.ComplexityLE p ∧ T.normBound ≤ 1 ∧
        γ ≤ ‖finiteComplexMean (fun n : Fin (K * q) =>
          (v (n.val : ZMod q) : ℂ) * star (T.eval (fun _ => (n.val : ℤ))))‖

/-- Preserve the Lipschitz constant when conjugating a complex observable. -/
theorem originalIntervalAdapter_lipschitz_star {X : Type*} [MetricSpace X]
    (F : C(X, ℂ)) {K : ℝ≥0} (hF : LipschitzWith K F) :
    LipschitzWith K (star F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (star (F x)) (star (F y)) ≤ (K : ℝ) * dist x y
  rw [Complex.star_def, Complex.dist_conj_conj]
  exact hF.dist_le_mul x y

/-- A uniform bounded-complexity niltest inverse yields precisely the native
interval inverse interface. The model step is unchanged, and all model data
are fixed before `q`, `K`, or `v`. -/
theorem native_periodic_interval_inverse_of_original_niltests
    (s d : ℕ) (hs : 1 ≤ s)
    (hinverse : HasUniformOriginalIntervalNiltestInverse s d) :
    HasNativePeriodicIntervalInverse.{0} s d := by
  intro δ hδ
  obtain ⟨p, hp, γ, hγ, hinv⟩ := hinverse δ hδ
  obtain ⟨n, hn, models, Lip, _hLip, hmenu⟩ :=
    exists_finite_native_linear_menu s hs hp
  refine ⟨n, hn, models, (fun _ => Lip), γ, hγ, ?_⟩
  intro q _ K v hv hnorm
  obtain ⟨A, T, hT, hTnorm, hcorr⟩ := hinv q K v hv hnorm
  obtain ⟨i, obs, g, x, hobs, hobsLip, heval⟩ := hmenu A T hT hTnorm
  refine ⟨i, ?_⟩
  letI := (models i).metric
  refine ⟨star obs, g, x, ?_, originalIntervalAdapter_lipschitz_star obs hobsLip, ?_⟩
  · intro y
    simpa only [ContinuousMap.star_apply, norm_star] using hobs y
  · simpa only [ContinuousMap.star_apply, heval] using hcorr

end Hindman168
