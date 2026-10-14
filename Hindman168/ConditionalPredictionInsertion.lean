import Hindman168.MasterSquareRootGapLengths

/-!
# Uniform insertion error with original prime-only restrictions

Actual original and auxiliary lengths may depend on the prime tuple.
Only a uniform lower length is used for their error budget. The original
prime law and its event restriction retain their original coefficients:
no division by a good-event probability is used.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def predictionUniformInsertionCap {b d h : ℕ}
    (X W : ℕ) (Tmin R : Fin b → ℕ) (dir : Fin h → Fin b × CubeVertex d) : ℝ :=
  translationError X W (predictionRootDisplacementCap dir R) +
    ∑ q, ∑ j : Fin d, ((h : ℝ) * |(cubeShiftDirection j : ℝ)|) *
      (2 / (Nat.sqrt (Tmin q) : ℝ))

theorem predictionInsertionErrorCap_le_uniform {b d h : ℕ}
    (X W : ℕ) (T Tmin R : Fin b → ℕ) (dir : Fin h → Fin b × CubeVertex d)
    (hmin : ∀ q, 0 < Tmin q) (hT : ∀ q, Tmin q ≤ T q) :
    predictionInsertionErrorCap X W T dir (fun q => (R q : ℝ))
        (fun q => (Nat.sqrt (T q) : ℝ)) ≤ predictionUniformInsertionCap X W Tmin R dir := by
  rw [predictionInsertionErrorCap_sqrt_eq]
  unfold predictionUniformInsertionCap
  refine add_le_add le_rfl ?_
  apply Finset.sum_le_sum
  intro q _
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have ht := lt_of_lt_of_le (hmin q) (hT q)
  refine (nat_sqrt_relative_loss ht).trans ?_
  have hl : (0 : ℝ) < Nat.sqrt (Tmin q) := by exact_mod_cast Nat.sqrt_pos.mpr (hmin q)
  exact div_le_div_of_nonneg_left (by norm_num) hl
    (by exact_mod_cast Nat.sqrt_le_sqrt (hT q))

theorem prediction_uniform_insertion_cap_rapid {α : Type*} {l : Filter α}
    {b d h : ℕ} (dir : Fin h → Fin b × CubeVertex d)
    {X W V : α → ℕ} {Tmin R : α → Fin b → ℕ}
    (hV : ∀ᶠ w in l, 1 ≤ V w)
    (hroot : PowerDominates l (fun w => (X w : ℝ))
      (fun w => (samplingSize (W w) 0 (predictionRootDisplacementCap dir (R w)) (V w) : ℝ)))
    (hshift : ∀ q, PowerDominates l (fun w => (Tmin w q : ℝ)) (fun w => (V w : ℝ))) :
    RapidlySmall l (fun w => (V w : ℝ))
      (fun w => predictionUniformInsertionCap (X w) (W w) (Tmin w) (R w) dir) := by
  have hr := translationError_rapid hroot hV
  have hs (q : Fin b) : RapidlySmall l (fun w => (V w : ℝ))
      (fun w => 2 / (Nat.sqrt (Tmin w q) : ℝ)) := by
    have hsq := (hshift q).nat_sqrt (hV.mono (fun w hw => by exact_mod_cast (by omega : 0 ≤ V w)))
    have hpos : ∀ᶠ w in l, 0 < Nat.sqrt (Tmin w q) := by
      filter_upwards [(hsq 0).bound (by norm_num : (0 : ℝ) < 1)] with w hw
      simp only [pow_zero, Real.norm_eq_abs, abs_one,
        abs_of_nonneg (Nat.cast_nonneg (Nat.sqrt (Tmin w q)) : (0 : ℝ) ≤ Nat.sqrt (Tmin w q)),
        one_mul] at hw
      exact_mod_cast (lt_of_lt_of_le zero_lt_one hw)
    apply rapid_of_polynomial_majorant hsq
      (hpos.mono (fun _ hw => by exact_mod_cast hw))
      (hV.mono (fun _ hw => ⟨by exact_mod_cast hw, le_rfl⟩)) 0 (by norm_num : (0 : ℝ) < 2)
    filter_upwards [hpos] with w hw
    simp only [pow_zero, mul_one]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / (Nat.sqrt (Tmin w q) : ℝ))]
  have hsum := RapidlySmall.finset_sum Finset.univ
    (fun q w => ∑ j : Fin d, ((h : ℝ) * |(cubeShiftDirection j : ℝ)|) *
      (2 / (Nat.sqrt (Tmin w q) : ℝ))) (fun q _ =>
      RapidlySmall.finset_sum Finset.univ _ (fun j _ =>
        (hs q).const_mul ((h : ℝ) * |(cubeShiftDirection j : ℝ)|)))
  intro C
  exact (hr C).add (hsum C)

theorem conditional_square_root_insertion_rapid {α β : Type*} {l : Filter α}
    {b d h : ℕ} (dir : Fin h → Fin b × CubeVertex d)
    {X W V : α → ℕ} {Tmin R : α → Fin b → ℕ}
    (ρ : α → Mass β) (E : α → β → Prop)
    (A : α → β → Fin b × Fin d × Bool → ℤ) (T : α → β → Fin b → ℕ)
    (M : α → β → Fin b → ℤ) (G Ω : α → β → ReplicaCubeRow b d → ℤ → ℝ) (B : ℕ)
    (hρ : ∀ w x, 0 ≤ ρ w x) (htρ : ∀ w, total (ρ w) = 1)
    (hV : ∀ᶠ w in l, 1 ≤ V w) (hW : ∀ᶠ w in l, 0 < W w)
    (hroot : PowerDominates l (fun w => (X w : ℝ))
      (fun w => (samplingSize (W w) 0 (predictionRootDisplacementCap dir (R w)) (V w) : ℝ)))
    (hshift : ∀ q, PowerDominates l (fun w => (Tmin w q : ℝ)) (fun w => (V w : ℝ)))
    (hT : ∀ᶠ w in l, ∀ x ∈ (ρ w).support, E w x → ∀ q, Tmin w q ≤ T w x q)
    (hM : ∀ᶠ w in l, ∀ x ∈ (ρ w).support, E w x → ∀ q, (W w : ℤ) ∣ M w x q)
    (hR : ∀ᶠ w in l, ∀ x ∈ (ρ w).support, E w x → ∀ q,
      |(M w x q : ℝ)| * T w x q ≤ R w q)
    (hG : ∀ᶠ w in l, ∀ x ∈ (ρ w).support, E w x → ∀ base y,
      |G w x base y| ≤ (V w : ℝ) ^ B) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w =>
      expectation (ρ w) (fun x => if E w x then
        expectation (piMass (predictionOriginalColumnMass (X w) (W w) (A w x) (T w x)))
          (fun z => expectation (predictionSquareRootPairMass dir (T w x))
            (fun v => predictionEliminationIntegrand (M w x) dir ∅ z v (G w x) (Ω w x))) else 0) -
      expectation (ρ w) (fun x => if E w x then
        expectation (piMass (predictionOriginalColumnMass (X w) (W w) (A w x) (T w x)))
          (fun z => ∏ base, G w x base (replicaCubeEval (M w x) base z)) else 0)) := by
  have hcap := prediction_uniform_insertion_cap_rapid dir hV hroot hshift
  have hmin : ∀ᶠ w in l, ∀ q, 0 < Tmin w q := by
    apply eventually_all.mpr
    intro q
    filter_upwards [((hshift q) 0).bound (by norm_num : (0 : ℝ) < 1)] with w hw
    simp only [pow_zero, Real.norm_eq_abs, abs_one,
      abs_of_nonneg (Nat.cast_nonneg (Tmin w q) : (0 : ℝ) ≤ Tmin w q), one_mul] at hw
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hw)
  apply (hcap.mul_power (hV.mono (fun w hw => by exact_mod_cast (by omega : 0 < V w)))
    (B * Fintype.card (ReplicaCubeRow b d))).of_abs_le
  filter_upwards [sampling_eventually_valid hroot hW, hmin, hT, hM, hR, hG, hW]
    with w hv hm ht hmw hr hg hww
  have hnonneg : 0 ≤ predictionUniformInsertionCap (X w) (W w) (Tmin w) (R w) dir := by
    unfold predictionUniformInsertionCap translationError
    apply add_nonneg
    · exact div_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _)
        (sub_nonneg.mpr hv.2.1.le))
    · exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
  have hb := expectation_difference_support_bound (ρ w) (hρ w)
    (fun x => if E w x then
      expectation (piMass (predictionOriginalColumnMass (X w) (W w) (A w x) (T w x)))
        (fun z => expectation (predictionSquareRootPairMass dir (T w x))
          (fun v => predictionEliminationIntegrand (M w x) dir ∅ z v (G w x) (Ω w x))) else 0)
    (fun x => if E w x then
      expectation (piMass (predictionOriginalColumnMass (X w) (W w) (A w x) (T w x)))
        (fun z => ∏ base, G w x base (replicaCubeEval (M w x) base z)) else 0)
    (((V w : ℝ) ^ B) ^ Fintype.card (ReplicaCubeRow b d) *
      predictionUniformInsertionCap (X w) (W w) (Tmin w) (R w) dir) (fun x hx => by
        by_cases he : E w x
        · simp only [if_pos he]
          have hactual : ∀ q, 0 < T w x q := fun q => (hm q).trans_le (ht x hx he q)
          exact (prediction_square_root_initial_insertion_error (X w) (W w) (A w x) (T w x)
            (M w x) dir (fun q => (R w q : ℝ)) (G w x) (Ω w x)
            (pow_nonneg (Nat.cast_nonneg _) B) (hg x hx he) hv.1 hww hv.2.1 hactual
            (hmw x hx he) (hr x hx he)).trans
              (mul_le_mul_of_nonneg_left
                (predictionInsertionErrorCap_le_uniform (X w) (W w) (T w x) (Tmin w) (R w) dir hm
                  (ht x hx he)) (pow_nonneg (pow_nonneg (Nat.cast_nonneg _) B) _))
        · simp only [if_neg he, sub_self, abs_zero]
          exact mul_nonneg (pow_nonneg (pow_nonneg (Nat.cast_nonneg _) B) _) hnonneg)
  simp only [htρ w, one_mul, ← pow_mul] at hb
  exact hb.trans (le_abs_self _)

end Hindman168
