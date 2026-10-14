import Hindman168.PredictionSquareRootIntervals
import Hindman168.JointSamplingAsymptotics

/-!
# Vanishing original-versus-translated prediction error

The insertion error is derived from original cutoff and interval growth.
Fixed polynomial sup bounds are absorbed by the every-inverse-power rate.
These are concrete square-root interval averages and actual cube products,
not a theorem assuming the insertion difference is already small.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def predictionRootDisplacementCap {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (R : Fin b → ℕ) : ℕ :=
  ∑ i, (cubeRootDirection (dir i).2.val).natAbs * R (dir i).1

theorem predictionInsertionErrorCap_sqrt_eq {b d h : ℕ}
    (X W : ℕ) (T R : Fin b → ℕ) (dir : Fin h → Fin b × CubeVertex d) :
    predictionInsertionErrorCap X W T dir (fun q => (R q : ℝ))
        (fun q => (Nat.sqrt (T q) : ℝ)) =
      translationError X W (predictionRootDisplacementCap dir R) +
        ∑ q, ∑ j : Fin d, ((h : ℝ) * |(cubeShiftDirection j : ℝ)|) *
          (2 * (Nat.sqrt (T q) : ℝ) / T q) := by
  unfold predictionInsertionErrorCap translationError predictionRootDisplacementCap
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem prediction_square_root_insertion_cap_rapid {α : Type*} {l : Filter α}
    {b d h : ℕ} (dir : Fin h → Fin b × CubeVertex d)
    {X W V : α → ℕ} {T R : α → Fin b → ℕ}
    (hV : ∀ᶠ w in l, 1 ≤ V w)
    (hroot : PowerDominates l (fun w => (X w : ℝ))
      (fun w => (samplingSize (W w) 0 (predictionRootDisplacementCap dir (R w)) (V w) : ℝ)))
    (hshift : ∀ q, PowerDominates l (fun w => (T w q : ℝ)) (fun w => (V w : ℝ))) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w =>
      predictionInsertionErrorCap (X w) (W w) (T w) dir (fun q => (R w q : ℝ))
        (fun q => (Nat.sqrt (T w q) : ℝ))) := by
  have hr := translationError_rapid hroot hV
  have hs (q : Fin b) (j : Fin d) :=
    (nat_sqrt_translation_loss_rapid (hshift q)
      (hV.mono (fun _ hw => ⟨by exact_mod_cast hw, le_rfl⟩))).const_mul
      ((h : ℝ) * |(cubeShiftDirection j : ℝ)|)
  have hsum := RapidlySmall.finset_sum Finset.univ
    (fun q w => ∑ j : Fin d, ((h : ℝ) * |(cubeShiftDirection j : ℝ)|) *
      (2 * (Nat.sqrt (T w q) : ℝ) / T w q)) (fun q _ =>
      RapidlySmall.finset_sum Finset.univ _ (fun j _ => hs q j))
  intro C
  simpa only [predictionInsertionErrorCap_sqrt_eq] using (hr C).add (hsum C)

theorem prediction_square_root_initial_insertion_rapid {α : Type*} {l : Filter α}
    {b d h : ℕ} (dir : Fin h → Fin b × CubeVertex d)
    {X W V : α → ℕ} {T R : α → Fin b → ℕ}
    (A : α → Fin b × Fin d × Bool → ℤ) (M : α → Fin b → ℤ)
    (G Ω : α → ReplicaCubeRow b d → ℤ → ℝ) (B : ℕ)
    (hV : ∀ᶠ w in l, 1 ≤ V w) (hW : ∀ᶠ w in l, 0 < W w)
    (hroot : PowerDominates l (fun w => (X w : ℝ))
      (fun w => (samplingSize (W w) 0 (predictionRootDisplacementCap dir (R w)) (V w) : ℝ)))
    (hshift : ∀ q, PowerDominates l (fun w => (T w q : ℝ)) (fun w => (V w : ℝ)))
    (hM : ∀ᶠ w in l, ∀ q, (W w : ℤ) ∣ M w q)
    (hR : ∀ᶠ w in l, ∀ q, |(M w q : ℝ)| * T w q ≤ R w q)
    (hG : ∀ᶠ w in l, ∀ base y, |G w base y| ≤ (V w : ℝ) ^ B) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w =>
      expectation (piMass (predictionOriginalColumnMass (X w) (W w) (A w) (T w)))
        (fun z => expectation (predictionSquareRootPairMass dir (T w))
          (fun v => predictionEliminationIntegrand (M w) dir ∅ z v (G w) (Ω w))) -
      expectation (piMass (predictionOriginalColumnMass (X w) (W w) (A w) (T w)))
        (fun z => ∏ base, G w base (replicaCubeEval (M w) base z))) := by
  have hcap := prediction_square_root_insertion_cap_rapid dir hV hroot hshift
  have ht : ∀ᶠ w in l, ∀ q, 0 < T w q := by
    apply eventually_all.mpr
    intro q
    filter_upwards [((hshift q) 0).bound (by norm_num : (0 : ℝ) < 1)] with w hw
    simp only [pow_zero, Real.norm_eq_abs, abs_one,
      abs_of_nonneg (Nat.cast_nonneg (T w q) : (0 : ℝ) ≤ T w q), one_mul] at hw
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hw)
  apply (hcap.mul_power
    (hV.mono (fun w hw => by exact_mod_cast (by omega : 0 < V w)))
    (B * Fintype.card (ReplicaCubeRow b d))).of_abs_le
  filter_upwards [sampling_eventually_valid hroot hW, ht, hM, hR, hG, hW]
    with w hv htw hMw hRw hGw hWw
  have he := prediction_square_root_initial_insertion_error (X w) (W w) (A w) (T w)
    (M w) dir (fun q => (R w q : ℝ)) (G w) (Ω w)
    (pow_nonneg (Nat.cast_nonneg _) B) hGw hv.1 hWw
    hv.2.1 htw hMw hRw
  rw [← pow_mul] at he
  exact he.trans (le_abs_self _)

end Hindman168
