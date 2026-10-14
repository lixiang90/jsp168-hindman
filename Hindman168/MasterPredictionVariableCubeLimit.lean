import Hindman168.VariableCubePadding

/-!
# Original cube product vanishes for independent replica dimensions

Unused ambient rows carry one and unused shifts integrate to mass one.
The original root and every real row use the same block's divisor mask,
as in the dual-test algebra. Only actual supported retained prime tuples
need length and W-divisibility conditions. All ambient limits and required
positivity are derived, not supplied convergence premises.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def masterPredictionVariableCubeAverage {N r b : ℕ} {dim : Fin b → ℕ}
    (F : MasterParameterFamily) (root : ℕ → Fin N) (primeGap : ℕ → Fin r → ℕ)
    (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (A : ℕ → (Fin r → ℕ) → VariableReplicaCubeColumn dim → ℤ)
    (T : ℕ → (Fin r → ℕ) → Fin b → ℕ) (E : ℕ → (Fin r → ℕ) → Prop)
    (G : ℕ → (Fin r → ℕ) → VariableReplicaCubeRow dim → ℤ → ℝ) (w : ℕ) : ℝ :=
  expectation (masterPrimeSlotsMass F w (primeGap w)) (fun x => if E w x then
    expectation (piMass (variablePredictionOriginalColumnMass (F.cutoff w (root w).val)
      (primorial w) (A w x) (T w x)))
      (fun z => ∏ row, G w x row (variableReplicaCubeEval
        (fun q => predictionCubeModulus w (s w q) (f q) x) row z)) else 0)

theorem MasterParameterConditions.prediction_variable_cube_product_tendsto
    {n N m r b d L : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F)
    (dim : Fin b → ℕ) (hd : ∀ q, dim q ≤ d)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
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
    (A : ℕ → (Fin r → ℕ) → VariableReplicaCubeColumn dim → ℤ)
    (T : ℕ → (Fin r → ℕ) → Fin b → ℕ) (E : ℕ → (Fin r → ℕ) → Prop)
    (hT : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      E w x → ∀ q, masterShiftLengthLowerBound F w (replicaGap w q).val (k q) ≤ T w x q)
    (hM : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      E w x → ∀ q, (primorial w : ℤ) ∣ predictionCubeModulus w (s w q) (f q) x)
    (hR : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      E w x → ∀ q,
        |(predictionCubeModulus w (s w q) (f q) x : ℝ)| * T w x q ≤ F.gap w (replicaGap w q).val)
    (G : ℕ → (Fin r → ℕ) → VariableReplicaCubeRow dim → ℤ → ℝ)
    (hroot : ∀ w x, G w x none = fun t =>
      integerDivisorMask (masterPredictionBaseDivisorMass F C (fun w _ => label w) w (none : ReplicaCubeRow b d)) t - 1)
    (hbound : ∀ᶠ w in atTop, ∀ x (row : Σ q : Fin b, CubeVertex (dim q)) t,
      |G w x (some row) t| ≤ 1 + integerDivisorMask
        (masterPredictionBaseDivisorMass F C (fun w _ => label w) w (none : ReplicaCubeRow b d)) t) :
    Tendsto (masterPredictionVariableCubeAverage F root (fun w j => primeGap w j) s f A T E G)
      atTop (𝓝 0) := by
  let dir : Fin (Fintype.card (Fin b × CubeVertex d)) → Fin b × CubeVertex d :=
    (Fintype.equivFin (Fin b × CubeVertex d)).symm
  let fullLabel : ℕ → ReplicaCubeRow b d → Fin m := fun w _ => label w
  let fullA w x := variableCubePaddedLocations hd (A w x)
  let fullG w x := embeddedValue (variableCubeRowEmbedding hd) (G w x) (fun _ => 1)
  let V w := masterCommonTailBudget F w (tail w)
  have hfulltail : ∀ᶠ w in atTop, ∀ base, (C w).tail (fullLabel w base) ⊆ tail w :=
    htail.mono (fun _ hw _ => hw)
  have hdiv : ∀ᶠ w in atTop, ∀ base,
      tailBound ((C w).tailCutoffs (F.cutoff w) (fullLabel w base)) ≤ V w :=
    hfulltail.mono (fun w hw base => hF.common_tail_divisor_budget (C w) w _ _ (hw base))
  have hmask := hF.prediction_masks_eventually_bounded C hN fullLabel V hdiv
  have hfullroot : ∀ w x, fullG w x none = fun t =>
      integerDivisorMask (masterPredictionBaseDivisorMass F C fullLabel w none) t - 1 := by
    intro w x
    change embeddedValue (variableCubeRowEmbedding hd) (G w x) (fun _ => 1)
      (variableCubeRowEmbedding hd none) = _
    rw [embeddedValue_apply _ (variableCubeRowEmbedding_injective hd)]
    exact hroot w x
  have hfullbound : ∀ᶠ w in atTop, ∀ x i t, |fullG w x (some (dir i)) t| ≤
      1 + integerDivisorMask (masterPredictionBaseDivisorMass F C fullLabel w (some (dir i))) t := by
    filter_upwards [hbound, hmask] with w hb hm
    intro x i t
    by_cases hr : some (dir i) ∈ Set.range (variableCubeRowEmbedding hd)
    · obtain ⟨row, he⟩ := hr
      change |embeddedValue (variableCubeRowEmbedding hd) (G w x) (fun _ => 1) (some (dir i)) t| ≤ _
      rw [← he, embeddedValue_apply _ (variableCubeRowEmbedding_injective hd)]
      cases row with
      | none => simp [variableCubeRowEmbedding] at he
      | some row => exact hb x row t
    · change |embeddedValue (variableCubeRowEmbedding hd) (G w x) (fun _ => 1) (some (dir i)) t| ≤ _
      rw [embeddedValue_outside _ _ _ _ hr]
      simp only [abs_one]
      linarith [(hm (some (dir i)) t).1]
  have hfixed := hF.prediction_original_cube_product_tendsto dir
    (Fintype.equivFin (Fin b × CubeVertex d)).symm.bijective C hN fullLabel tail hfulltail
    root replicaGap primeGap k htailroot htailreplica htailprime hgap polys hpolys s e hs f hf
    fullA T E hT hM hR fullG hfullroot hfullbound
  have hminpos : ∀ᶠ w in atTop, ∀ q, 0 < masterShiftLengthLowerBound F w (replicaGap w q).val (k q) := by
    apply eventually_all.mpr
    intro q
    have hb := (hF.quotient_shift_growth (fun w => replicaGap w q) (k q)).eventually_bound
      (Eventually.of_forall (fun _ => Nat.cast_nonneg _))
      (Eventually.of_forall (fun _ => by positivity)) 0 (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hb] with w hw
    simp only [pow_zero, one_mul] at hw
    have hn : 1 ≤ masterShiftLengthLowerBound F w (replicaGap w q).val (k q) := by exact_mod_cast hw
    omega
  have havg : ∀ᶠ w in atTop,
      masterPredictionOriginalCubeAverage F root (fun w j => primeGap w j) s f fullA T E fullG w =
      masterPredictionVariableCubeAverage F root (fun w j => primeGap w j) s f A T E G w := by
    filter_upwards [hF.raw_cutoffs_valid, hminpos, hT] with w hv hp ht
    unfold masterPredictionOriginalCubeAverage masterPredictionVariableCubeAverage
    apply expectation_congr_support
    intro x hx
    split_ifs with he
    · exact variable_cube_padded_expectation hd _ _ (A w x) (T w x)
        (hv (root w).val (Finset.mem_range.mpr (root w).isLt)).2.2
        (fun q => (hp q).trans_le (ht x hx he q)) _ (G w x)
    · rfl
  exact hfixed.congr' havg

end Hindman168
