import Hindman168.PredictionConcreteBoxes
import Hindman168.PredictionDivisorSupBounds
import Hindman168.MasterPredictionInsertion

/-!
# Original cube row-product limit under the actual master prime law

The actual common-tail budget supplies consistent after-tail prime and shift
budgets before the root. Concrete original and square-root auxiliary boxes
identify the eliminated average with the inserted original law. Its insertion
error is derived from master growth, actual W-multiple moduli and original
support lengths. No desired small moment, prefactor, insertion or terminal
limit is assumed. This is a fixed-dimension cube lemma, not Prediction or the
finite sums/products theorem.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def masterPredictionOriginalCubeAverage {N r b d : ℕ}
    (F : MasterParameterFamily) (root : ℕ → Fin N) (primeGap : ℕ → Fin r → ℕ)
    (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (A : ℕ → (Fin r → ℕ) → Fin b × Fin d × Bool → ℤ)
    (T : ℕ → (Fin r → ℕ) → Fin b → ℕ) (E : ℕ → (Fin r → ℕ) → Prop)
    (G : ℕ → (Fin r → ℕ) → ReplicaCubeRow b d → ℤ → ℝ) (w : ℕ) : ℝ :=
  expectation (masterPrimeSlotsMass F w (primeGap w)) (fun x => if E w x then
    expectation (piMass (predictionOriginalColumnMass (F.cutoff w (root w).val)
      (primorial w) (A w x) (T w x)))
      (fun z => ∏ base, G w x base
        (replicaCubeEval (fun q => predictionCubeModulus w (s w q) (f q) x) base z)) else 0)

theorem conditionalFiniteAverage_support_event {α β : Type*} (μ : Mass α)
    (base : α → Mass β) (E : α → Prop) (g : α → β → ℝ) :
    conditionalFiniteAverage μ base (fun x => E x ∧ x ∈ μ.support) g =
      conditionalFiniteAverage μ base E g := by
  unfold conditionalFiniteAverage
  apply expectation_congr_support
  intro x hx
  simp only [hx, and_true]

theorem MasterParameterConditions.prediction_original_cube_product_tendsto
    {n N m r b d h L : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F)
    (dir : Fin h → Fin b × CubeVertex d) (hdir : Function.Bijective dir)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → ReplicaCubeRow b d → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, ∀ base, (C w).tail (label w base) ⊆ tail w)
    (root : ℕ → Fin N) (replicaGap : ℕ → Fin b → Fin N)
    (primeGap : ℕ → Fin r → Fin L) (k : Fin b → ℕ)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htailreplica : ∀ᶠ w in atTop, ∀ q, tail w ⊆ Finset.range (replicaGap w q).val)
    (htailprime : ∀ᶠ w in atTop, ∀ j, tail w ⊆ Finset.range (primeGap w j))
    (hgap : ∀ᶠ w in atTop, ∀ q, (replicaGap w q).val ≤ (root w).val)
    (polys : Finset (MvPolynomial (Fin r) ℤ)) (hpolys : ∀ p ∈ polys, p ≠ 0)
    (s : ℕ → Fin b → ℕ) (e : ℕ → Fin b → ℕ)
    (hs : ∀ᶠ w in atTop, ∀ q, s w q ∣ primorial w ^ e w q)
    (f : Fin b → MvPolynomial (Fin r) ℤ) (hf : ∀ q, f q ∈ polys)
    (A : ℕ → (Fin r → ℕ) → Fin b × Fin d × Bool → ℤ)
    (T : ℕ → (Fin r → ℕ) → Fin b → ℕ) (E : ℕ → (Fin r → ℕ) → Prop)
    (hT : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      E w x → ∀ q, masterShiftLengthLowerBound F w (replicaGap w q).val (k q) ≤ T w x q)
    (hM : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      E w x → ∀ q, (primorial w : ℤ) ∣ predictionCubeModulus w (s w q) (f q) x)
    (hR : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      E w x → ∀ q,
        |(predictionCubeModulus w (s w q) (f q) x : ℝ)| * T w x q ≤ F.gap w (replicaGap w q).val)
    (G : ℕ → (Fin r → ℕ) → ReplicaCubeRow b d → ℤ → ℝ)
    (hroot : ∀ w x, G w x none = fun t =>
      integerDivisorMask (masterPredictionBaseDivisorMass F C label w none) t - 1)
    (hbound : ∀ᶠ w in atTop, ∀ x i t, |G w x (some (dir i)) t| ≤
      1 + integerDivisorMask (masterPredictionBaseDivisorMass F C label w (some (dir i))) t) :
    Tendsto (masterPredictionOriginalCubeAverage F root (fun w j => primeGap w j) s f A T E G)
      atTop (𝓝 0) := by
  let V w := masterCommonTailBudget F w (tail w)
  let Tmin w q := masterShiftLengthLowerBound F w (replicaGap w q).val (k q)
  let H := predictionBoxRootColumns b d h
  let index w (_ : Fin (Fintype.card (CopiedReplicaCubeColumn b d h))) := root w
  let loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ :=
    fun w x => predictionBoxLocationFin (A w x)
  let len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ :=
    fun w x => predictionBoxLengthFin dir (T w x)
  let lower w := predictionBoxLengthFin dir (Tmin w)
  let E' w x := E w x ∧ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support
  let stage w := masterPredictionStageAverage F C label (fun w j => primeGap w j)
    s f dir H index loc len E G w ∅
  have hV2 : ∀ᶠ w in atTop, 2 ≤ V w :=
    Eventually.of_forall (fun w => masterCommonTailBudget_ge_two F w (tail w))
  have hV : ∀ᶠ w in atTop, 1 ≤ V w := hV2.mono (fun _ hw => by omega)
  have hVr : ∀ᶠ w in atTop, V w ≤ F.auxiliary w (root w).val :=
    htailroot.mono (fun w hw => hF.common_tail_budget_le_auxiliary w _ _ hw)
  have hVq : ∀ᶠ w in atTop, ∀ q, V w ≤ F.auxiliary w (replicaGap w q).val :=
    htailreplica.mono (fun w hw q => hF.common_tail_budget_le_auxiliary w _ _ (hw q))
  have hdiv : ∀ᶠ w in atTop, ∀ base,
      tailBound ((C w).tailCutoffs (F.cutoff w) (label w base)) ≤ V w :=
    htail.mono (fun w hw base => hF.common_tail_divisor_budget (C w) w _ _ (hw base))
  have hqgrowth (q : Fin b) : PowerDominates atTop (fun w => (Tmin w q : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)) := by
    apply (hF.quotient_sqrt_sampling_growth (fun w => replicaGap w q) (k q)
      (hVq.mono (fun _ hw => hw q))).mono_right
    exact Eventually.of_forall (fun _ => ⟨Nat.cast_nonneg _, by exact_mod_cast Nat.sqrt_le_self _⟩)
  have hboxgrowth : ∀ j, j ∉ H → PowerDominates atTop (fun w => (lower w j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)) :=
    prediction_box_lower_growth dir Tmin V hqgrowth
  have hboxlen : ∀ᶠ w in atTop, ∀ x, E' w x → ∀ j, j ∉ H → lower w j ≤ len w x j := by
    filter_upwards [hT] with w hw
    intro x hx j _
    exact prediction_box_lengths_mono dir (Tmin w) (T w x) (hw x hx.2 hx.1) j
  have htailharm : ∀ᶠ w in atTop, ∀ j ∈ H, tail w ⊆ Finset.range (index w j).val :=
    htailroot.mono (fun _ hw _ _ => hw)
  have htrans := hF.prediction_common_tail_translated_tendsto dir C hN label primeGap tail
    htail htailprime polys hpolys s e hs f hf H index lower loc len E'
    htailharm hboxgrowth hboxlen prediction_box_auxiliary_columns
    (fun w x => prediction_box_locations_pair (A w x))
    (fun w x => prediction_box_lengths_pair dir (T w x)) hdir G hroot hbound
  have hstage (w : ℕ) : masterPredictionStageAverage F C label (fun w j => primeGap w j)
      s f dir H index loc len E' G w ∅ = stage w := by
    unfold masterPredictionStageAverage stage
    exact conditionalFiniteAverage_support_event _ _ _ _
  have htranslated : Tendsto stage atTop (𝓝 0) :=
    htrans.congr' (Eventually.of_forall hstage)
  have hsup := hF.prediction_tests_eventually_sup_bound C hN label V hV2 hdiv dir hdir.2
    G hroot hbound
  have hins := hF.prediction_original_insertion_rapid dir root replicaGap
    (fun w j => primeGap w j) k V hV hVr hVq hgap E A T
    (fun w x q => predictionCubeModulus w (s w q) (f q) x) G
    (fun w _ base t => 1 + integerDivisorMask (masterPredictionBaseDivisorMass F C label w base) t)
    2 hT hM hR (hsup.mono (fun _ hw x _ _ => hw x))
  have hdelta : RapidlySmall atTop (fun w => (V w : ℝ)) (fun w => stage w -
      masterPredictionOriginalCubeAverage F root (fun w j => primeGap w j) s f A T E G w) := by
    simpa only [stage, H, index, loc, len, prediction_box_stage_average,
      masterPredictionOriginalCubeAverage] using hins
  have hdelta0 : Tendsto (fun w => stage w -
      masterPredictionOriginalCubeAverage F root (fun w j => primeGap w j) s f A T E G w)
      atTop (𝓝 0) := by
    apply (isLittleO_one_iff ℝ).mp
    simpa only [pow_zero, inv_one] using hdelta 0
  convert htranslated.sub hdelta0 using 1 <;> simp

end Hindman168
