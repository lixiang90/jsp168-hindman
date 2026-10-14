import Hindman168.MasterInverseProjectionThreshold
import Hindman168.MasterCanonicalGlobalGowers

namespace Hindman168
open FiniteMass Filter NNReal
open scoped BigOperators Topology Classical
universe u

/-- The finite-list periodic interval inverse existence statement needed
by the paper. This is a proposition, not an axiom or a proved assertion.
All manifolds, bounds and positive correlation constants are fixed before
the interval length, cyclic order and unit input. -/
def HasNativePeriodicIntervalInverse (s d : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ L : ℕ, 0 < L ∧
    ∃ D : Fin L → NativeNilmanifoldData.{u} s, ∃ Lip : Fin L → ℝ≥0,
    ∃ γ : ℝ, 0 < γ ∧ ∀ (q : ℕ) [NeZero q] (K : ℕ) (v : ZMod q → ℝ),
      (∀ z, |v z| ≤ 1) → δ / 4 ≤ integerIntervalPeriodicGowersValue q d (K * q) v →
      ∃ i : Fin L,
        letI := (D i).metric
        letI : TopologicalSpace ((D i).G ⧸ (D i).Γ) :=
          (D i).metric.toUniformSpace.toTopologicalSpace
        ∃ (obs : C((D i).G ⧸ (D i).Γ, ℂ)) (g x : (D i).G),
          (∀ z, ‖obs z‖ ≤ 1) ∧ LipschitzWith (Lip i) obs ∧
          γ ≤ ‖finiteComplexMean (fun n : Fin (K * q) =>
            (v (n.val : ZMod q) : ℂ) * obs (g ^ (n.val : ℤ) * x))‖

/-- Given the displayed inverse existence statement, one positive fine
projection threshold works before choosing N or any master data. -/
theorem native_interval_inverse_uniform_projection_threshold (s d : ℕ) (hd : 0 < d)
    (hinverse : HasNativePeriodicIntervalInverse.{u} s d) (δ : ℝ) (hδ : 0 < δ) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ {n N : ℕ} {A : Finset ℚ} {polys : Finset (MvPolynomial (Fin n) ℤ)}
        {F : MasterParameterFamily} (hF : MasterParameterConditions N A polys F)
        (U : Ultrafilter ℕ) (_hU : (U : Filter ℕ) ≤ atTop) (gap pivot : ℕ → Fin N)
        (_horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
        (h : boundedHilbertFamilies (fun w =>
          FiniteMassL2 (integerMass (F.cutoff w (pivot w).val) (primorial w))))
        (_hf : ∀ w y, |h.val w y| ≤ 1),
      ‖(nativeNilHilbertSubspace.{u} s F
        (fun w => integerMass (F.cutoff w (pivot w).val) (primorial w)) U gap).starProjection
          (hilbertFamilyToCompletion _ U h)‖ < κ →
      ∀ᶠ w in (U : Filter ℕ),
        letI : NeZero (F.gap w (gap w).val / (F.modulus w : ℕ)) :=
          ⟨Nat.ne_of_gt (hF.common_cyclic_order_positive w (gap w).val)⟩
        masterCompleteGlobalGowersValue F gap pivot w d (fun y => h.val w y) < δ := by
  obtain ⟨L, hL, D, Lip, γ, hγ, hinterval⟩ := hinverse δ hδ
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  let κ := δ ^ (2 ^ d) / 2 * γ
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  refine ⟨κ, hκ, ?_⟩
  intro n N A polys F hF U hU gap pivot horder h hf hp
  exact hF.interval_inverse_projection_norm_threshold s U hU gap pivot horder h hf
    D Lip d hd δ γ hδ hγ hinterval hp

end Hindman168
