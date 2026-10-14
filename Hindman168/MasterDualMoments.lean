import Hindman168.MasterNormalizedDualMajorantLimit
import Hindman168.PredictionDualMomentDomination

/-!
# Every fixed original normalized dual moment

One fixed master family contains the local template independently of the
moment order. The actual conditioned prime law and original quotient
shifts give the bound 2 A_d^b plus any positive error eventually. No
Jensen, moment-convergence or tail-probability premise is supplied.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def predictionDualThreshold (d : ℕ) : ℝ := (2 : ℝ) ^ (2 ^ d - 1)

noncomputable def masterSingleGoodDualTest {a N K : ℕ} (F : MasterParameterFamily)
    (d : ℕ) (gap : ℕ → Fin N) (J : Fin K → ℕ) (choice : ℕ → Fin K)
    (tests : Finset (MvPolynomial (Fin a) ℤ)) (den : MvPolynomial (Fin a) ℤ)
    (ε : ℕ → (Fin a → ℕ) → ℝ)
    (g : ℕ → (Fin a → ℕ) → CubeVertex d → ℤ → ℝ) (w : ℕ) (y : ℤ) : ℝ :=
  predictionSingleDualTest d (conditionMass
    (primeIndependentMass a (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper)
    (predictionLocalPrimeGoodEvent F tests den w)) (fun _ _ => 0)
    (fun x => F.gap w (gap w).val / (J (choice w) *
      (predictionCubeModulus w (F.modulus w : ℕ) den x).natAbs))
    (predictionCubeModulus w (F.modulus w : ℕ) den) (ε w) (g w) y

theorem master_single_good_dual_replica {a N K b : ℕ} (F : MasterParameterFamily)
    (d : ℕ) (gap : ℕ → Fin N) (J : Fin K → ℕ) (choice : ℕ → Fin K)
    (tests : Finset (MvPolynomial (Fin a) ℤ)) (den : MvPolynomial (Fin a) ℤ)
    (ε : ℕ → (Fin a → ℕ) → ℝ)
    (g : ℕ → (Fin a → ℕ) → CubeVertex d → ℤ → ℝ) (w : ℕ) (q : Fin b) (y : ℤ) :
    masterSingleGoodDualTest F d gap J choice tests den ε g w y =
      masterReplicaGoodDualTest F (fun _ : Fin b => d) (fun _ => a) (fun w _ => gap w)
        J (fun w _ => choice w) (fun _ => tests) (fun _ => den)
        (fun w _ => ε w) (fun w _ => g w) w q y := rfl

theorem predictionDualThreshold_ge_one (d : ℕ) : 1 ≤ predictionDualThreshold d := by
  unfold predictionDualThreshold
  exact one_le_pow₀ (by norm_num)

theorem MasterParameterConditions.block_mask_eventually_nonneg {n N m : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (label : ℕ → Fin m) :
    ∀ᶠ w in atTop, ∀ y, 0 ≤ masterPredictionBlockMask F C label w y := by
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  intro y
  let Xs := (C w).tailCutoffs (F.cutoff w) (label w)
  have hv : ValidCutoffs Xs (primorial w) := chain_tailCutoffs_valid (C w) (F.cutoff w)
    (primorial w) (hN w) (fun j hj => ⟨(hw j hj).1, (hw j hj).2.1⟩) (label w)
  unfold masterPredictionBlockMask
  rw [integerDivisorMask_expectation]
  exact expectation_nonneg _ _ (tailMass_nonneg (primorial_pos w) Xs hv)
    (fun _ => by split_ifs <;> positivity)

theorem MasterParameterConditions.normalized_single_dual_moment_eventually_le
    {n a N m d b K : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root gap : ℕ → Fin N)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htailgap : ∀ᶠ w in atTop, tail w ⊆ Finset.range (gap w).val)
    (J : Fin K → ℕ) (hJ : ∀ k, 1 ≤ J k) (choice : ℕ → Fin K)
    (tests : Finset (MvPolynomial (Fin a) ℤ))
    (den : MvPolynomial (Fin a) ℤ) (hden : den ∈ tests)
    (masterSlot : Fin a → Fin n) (hmasterSlot : Function.Injective masterSlot)
    (hinclude : ∀ f ∈ tests, MvPolynomial.rename masterSlot f ∈ D)
    (ε : ℕ → (Fin a → ℕ) → ℝ) (hε : ∀ᶠ w in atTop, ∀ x, |ε w x| ≤ 1)
    (g : ℕ → (Fin a → ℕ) → CubeVertex d → ℤ → ℝ)
    (hg : ∀ᶠ w in atTop, ∀ x S y, |g w x S y| ≤ 1 + masterPredictionBlockMask F C label w y)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ w in atTop, expectation (integerMass (F.cutoff w (root w).val) (primorial w))
      (fun y => (1 + masterPredictionBlockMask F C label w y) *
        |masterSingleGoodDualTest F d gap J choice tests den ε g w y| ^ b) ≤
      2 * predictionDualThreshold d ^ b + δ := by
  let arity : Fin b → ℕ := fun _ => a
  let e : (Σ _q : Fin b, Fin a) ≃ Fin (Fintype.card (Σ _q : Fin b, Fin a)) :=
    Fintype.equivFin _
  have hm := hF.normalized_dual_majorant_product_tendsto (d := d) hD arity e C hN
    label tail htail root (fun w _ => gap w) htailroot
    (htailgap.mono (fun _ hw _ => hw)) J hJ (fun w _ => choice w)
    (fun _ => tests) (fun _ => den) (fun _ => hden) (fun _ => masterSlot)
    (fun _ => hmasterSlot) (fun _ f hf => hinclude f hf)
  have hc : (2 : ℝ) ^ (1 + b * (2 ^ d - 1)) = 2 * predictionDualThreshold d ^ b := by
    rw [pow_add, pow_one]
    unfold predictionDualThreshold
    rw [← pow_mul]
    rw [Nat.mul_comm]
  rw [hc] at hm
  have hupper := hm.eventually (Iio_mem_nhds (by linarith :
    2 * predictionDualThreshold d ^ b < 2 * predictionDualThreshold d ^ b + δ))
  filter_upwards [hupper, hε, hg, hF.block_mask_eventually_nonneg C hN label,
    hF.raw_cutoffs_valid] with w hu he hgw hν hw
  let μ := conditionMass
    (primeIndependentMass a (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper)
    (predictionLocalPrimeGoodEvent F tests den w)
  have hμ : ∀ x, 0 ≤ μ x := conditionMass_nonneg _ _ (primeIndependentMass_nonneg _ _ _)
  let T (x : Fin a → ℕ) := F.gap w (gap w).val / (J (choice w) *
    (predictionCubeModulus w (F.modulus w : ℕ) den x).natAbs)
  have hρ : ∀ y, 0 ≤ integerMass (F.cutoff w (root w).val) (primorial w) y :=
    integerMass_nonneg (hw (root w).val (Finset.mem_range.mpr (root w).isLt)).2.2
  have hd := prediction_single_dual_power_domination d b μ hμ (fun _ _ => 0) T
    (predictionCubeModulus w (F.modulus w : ℕ) den) (ε w) he (g w)
    (masterPredictionBlockMask F C label w) hν hgw _ hρ
  refine hd.trans ?_
  change expectation (integerMass (F.cutoff w (root w).val) (primorial w))
    (fun y => (1 + masterPredictionBlockMask F C label w y) * ∏ _q : Fin b,
      masterSingleGoodDualTest F d gap J choice tests den (fun _ _ => 1)
        (fun w _ _ y => 1 + masterPredictionBlockMask F C label w y) w y) ≤ _
  have hprod (y : ℤ) : (∏ _q : Fin b,
      masterSingleGoodDualTest F d gap J choice tests den (fun _ _ => 1)
        (fun w _ _ y => 1 + masterPredictionBlockMask F C label w y) w y) =
      ∏ q : Fin b, masterReplicaGoodDualTest F (fun _ => d) (fun _ => a)
        (fun w _ => gap w) J (fun w _ => choice w) (fun _ => tests) (fun _ => den)
        (fun _ _ _ => 1) (fun w _ _ _ y => 1 + masterPredictionBlockMask F C label w y) w q y := by
    apply Finset.prod_congr rfl
    intro q _
    exact master_single_good_dual_replica F d gap J choice tests den
      (fun _ _ => 1) (fun w _ _ y => 1 + masterPredictionBlockMask F C label w y) w q y
  simp_rw [hprod]
  exact hu.le

end Hindman168
