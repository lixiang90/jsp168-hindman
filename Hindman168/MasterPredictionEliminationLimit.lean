import Hindman168.MasterPredictionStageValidity

/-!
# Actual translated prediction product vanishes by ordered elimination

Every stage's squaring inequality is proved under the original restricted
prime law and actual auxiliary intervals. All prefactor bounds and the
terminal limit are derived from the master conditions. Finite backward
squaring therefore proves the initial translated-stage average tends to
zero. Initial translation insertion and the later dual-test application
are not supplied by this result.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

theorem MasterParameterConditions.prediction_translated_product_tendsto
    {n N m r b d h L : ℕ}
    (dir : Fin h → Fin b × CubeVertex d)
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (label : ℕ → ReplicaCubeRow b d → Fin m)
    (gap : ℕ → Fin r → Fin L) (V : ℕ → ℕ) (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hdivbudget : ∀ᶠ w in atTop, ∀ base, tailBound ((C w).tailCutoffs (F.cutoff w) (label w base)) ≤ V w)
    (hprimebudget : ∀ᶠ w in atTop, ∀ j, V w ≤ F.auxiliary w (gap w j))
    (T : Finset (MvPolynomial (Fin r) ℤ)) (hT : ∀ f ∈ T, f ≠ 0)
    (s : ℕ → Fin b → ℕ) (e : ℕ → Fin b → ℕ)
    (hs : ∀ᶠ w in atTop, ∀ v, s w v ∣ primorial w ^ e w v)
    (f : Fin b → MvPolynomial (Fin r) ℤ) (hf : ∀ v, f v ∈ T)
    (H : Finset (Fin (Fintype.card (CopiedReplicaCubeColumn b d h))))
    (index : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → Fin N)
    (Tmin : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (E : ℕ → (Fin r → ℕ) → Prop)
    (hharmbudget : ∀ᶠ w in atTop, ∀ j ∈ H, V w ≤ F.auxiliary w (index w j).val)
    (hlengthgrowth : ∀ j, j ∉ H → PowerDominates atTop (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)))
    (hlen : ∀ᶠ w in atTop, ∀ x, E w x → ∀ j, j ∉ H → Tmin w j ≤ len w x j)
    (haux : ∀ i bit, predictionColumnIndex (.inr (i, bit) : CopiedReplicaCubeColumn b d h) ∉ H)
    (hloc : ∀ w x i bit, loc w x (predictionColumnIndex (.inr (i, bit))) =
      loc w x (predictionColumnIndex (.inr (i, false))))
    (hpair : ∀ w x i bit, len w x (predictionColumnIndex (.inr (i, bit))) =
      len w x (predictionColumnIndex (.inr (i, false))))
    (hdir : Function.Bijective dir)
    (G : ℕ → (Fin r → ℕ) → ReplicaCubeRow b d → ℤ → ℝ)
    (hroot : ∀ w x, G w x none = fun t =>
      integerDivisorMask (masterPredictionBaseDivisorMass F C label w none) t - 1)
    (hbound : ∀ᶠ w in atTop, ∀ x i t, |G w x (some (dir i)) t| ≤
      1 + integerDivisorMask (masterPredictionBaseDivisorMass F C label w (some (dir i))) t) :
    Tendsto (fun w => masterPredictionStageAverage F C label (fun w j => gap w j)
      s f dir H index loc len E G w ∅) atTop (𝓝 0) := by
  let stages (j w : ℕ) := masterPredictionStageAverage F C label (fun w j => gap w j)
    s f dir H index loc len E G w (predictionDirectionPrefix h j)
  let stageCap (j : ℕ) : ℝ := if hj : j < h then
    ((2 ^ (copiedPredictionStageRowIndices dir (predictionDirectionPrefix h j)
      (some (dir ⟨j, hj⟩))).card : ℕ) : ℝ) + 1 else 0
  have hbase := hF.prediction_original_base_eventually_nonneg H index loc len
  have hpos := prediction_direction_lengths_eventually_positive H Tmin V len E haux hlengthgrowth hlen
  have hstep : ∀ j < h, ∀ᶠ w in atTop, |stages j w| ^ 2 ≤ stageCap j * |stages (j + 1) w| := by
    intro j hj
    let k : Fin h := ⟨j, hj⟩
    have hcap := hF.prediction_stage_prefactor_eventually_le dir C hN label gap V hV
      hdivbudget hprimebudget T hT s e hs f hf H index Tmin loc len E
      hharmbudget hlengthgrowth hlen haux hloc hpair
      (predictionDirectionPrefix h j) (some (dir k))
    filter_upwards [hcap, hbase, hpos, hbound] with w hc hb hp hg
    have hprime := hF.prime_slots_nonneg w (fun a => gap w a)
    have hmajorant (t : ℤ) : 0 ≤
        1 + integerDivisorMask (masterPredictionBaseDivisorMass F C label w (some (dir k))) t :=
      (abs_nonneg (G w (fun _ => 0) (some (dir k)) t)).trans (hg (fun _ => 0) k t)
    have hpn := master_prediction_stage_prefactor_nonneg F C label (fun w a => gap w a)
      s f dir H index loc len E w (predictionDirectionPrefix h j) (some (dir k))
      hprime (fun x _ z => hb x z) hmajorant
    have hcs := master_prediction_stage_step F C label (fun w a => gap w a)
      s f dir H index loc len E G w (predictionDirectionPrefix h j) k
      (predictionDirectionPrefix_fresh k) hdir.1 hprime (fun x _ z => hb x z)
      hp (fun x t => hg x k t)
    have hprefix : insert k (predictionDirectionPrefix h j) = predictionDirectionPrefix h (j + 1) :=
      (predictionDirectionPrefix_succ k).symm
    rw [hprefix] at hcs
    dsimp only [stages, stageCap]
    rw [dif_pos hj]
    calc
      _ ≤ masterPredictionStagePrefactor F C label (fun w a => gap w a)
          s f dir H index loc len E w (predictionDirectionPrefix h j) (some (dir k)) *
        masterPredictionStageAverage F C label (fun w a => gap w a)
          s f dir H index loc len E G w (predictionDirectionPrefix h (j + 1)) := hcs
      _ ≤ masterPredictionStagePrefactor F C label (fun w a => gap w a)
          s f dir H index loc len E w (predictionDirectionPrefix h j) (some (dir k)) *
        |masterPredictionStageAverage F C label (fun w a => gap w a)
          s f dir H index loc len E G w (predictionDirectionPrefix h (j + 1))| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hpn
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
  have hterminal : Tendsto (stages h) atTop (𝓝 0) := by
    simpa only [stages, predictionDirectionPrefix_full] using
      hF.prediction_stage_terminal_tendsto dir C hN label gap V hV hdivbudget hprimebudget
        T hT s e hs f hf H index Tmin loc len E hharmbudget hlengthgrowth hlen
        haux hloc hpair hdir.2 G hroot
  have hzero := finite_squared_chain_tendsto_zero h stages stageCap hstep hterminal
  simpa only [stages, predictionDirectionPrefix_zero] using hzero

end Hindman168
