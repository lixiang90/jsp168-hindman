import Hindman168.MasterNormalizedDualProductLimit
import Hindman168.MasterPredictionQuotientMajorantMean
import Hindman168.ConstantCubeLaw

/-!
# Normalized original dual-majorant products

Independent replicas keep their own local prime arities and denominators.
Original cube means and actual good-event probabilities imply the exact
one-plus majorant limit, including the root factor. The master family and
polynomial list stay fixed as the replica count varies.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem MasterParameterConditions.normalized_dual_majorant_product_tendsto {n r N m b d K : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0)
    (arity : Fin b → ℕ)
    (e : (Σ q, Fin (arity q)) ≃ Fin r)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N) (gap : ℕ → Fin b → Fin N)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htailgap : ∀ᶠ w in atTop, ∀ q, tail w ⊆ Finset.range (gap w q).val)
    (J : Fin K → ℕ) (hJ : ∀ a, 1 ≤ J a) (choice : ℕ → Fin b → Fin K)
    (tests : ∀ q, Finset (MvPolynomial (Fin (arity q)) ℤ))
    (den : ∀ q, MvPolynomial (Fin (arity q)) ℤ) (hden : ∀ q, den q ∈ tests q)
    (masterSlot : ∀ q, Fin (arity q) → Fin n) (hmasterSlot : ∀ q, Function.Injective (masterSlot q))
    (hinclude : ∀ q f, f ∈ tests q → MvPolynomial.rename (masterSlot q) f ∈ D)
    : Tendsto (fun w => expectation (integerMass (F.cutoff w (root w).val) (primorial w))
      (fun y => (1 + masterPredictionBlockMask F C label w y) *
        ∏ q, masterReplicaGoodDualTest F (fun _ => d) arity gap J choice tests den
          (fun _ _ _ => 1) (fun w _ _ _ y => 1 + masterPredictionBlockMask F C label w y) w q y))
      atTop (𝓝 ((2 : ℝ) ^ (1 + b * (2 ^ d - 1)))) := by
  let H w y := 1 + masterPredictionBlockMask F C label w y
  let ε : ℕ → ∀ q : Fin b, (Fin (arity q) → ℕ) → ℝ := fun _ _ _ => 1
  let g : ℕ → ∀ q : Fin b, (Fin (arity q) → ℕ) → CubeVertex d → ℤ → ℝ :=
    fun w _ _ _ y => H w y
  let f q := replicaPolynomialLift e q (den q)
  let globalGap w j := replicaPrimeGap e (gap w) j
  let E w x := ∀ q, predictionLocalPrimeGoodEvent F (tests q) (den q) w ((replicaPrimeSampleEquiv arity e) x q)
  have htailprime : ∀ᶠ w in atTop, ∀ j, tail w ⊆ Finset.range (globalGap w j).val :=
    htailgap.mono (fun _ hw j => hw (e.symm j).1)
  have hdenzero (q : Fin b) : den q ≠ 0 := by
    intro hz
    apply hD (MvPolynomial.rename (masterSlot q) (den q)) (hinclude q (den q) (hden q))
    rw [hz, MvPolynomial.rename_zero]
  let polys := Finset.univ.image f
  have hf : ∀ q, f q ∈ polys := fun q => Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩
  have hpolys : ∀ p ∈ polys, p ≠ 0 := by
    intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    exact replicaPolynomialLift_nonzero e q (den q) (hdenzero q)
  have hslots : ∀ᶠ w in atTop, ∀ q j, j ∈ (f q).vars →
      (globalGap w j).val = (gap w q).val := Eventually.of_forall (fun w q j hj =>
        congrArg Fin.val (replicaPolynomialLift_vars_gap e (gap w) q (den q) j hj))
  have hnonzero : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => globalGap w j)).support,
      E w x → ∀ q, MvPolynomial.eval (fun j => (x j : ℤ)) (f q) ≠ 0 := by
    apply Eventually.of_forall
    intro w x _ hx q
    rw [show f q = replicaPolynomialLift e q (den q) from rfl, replicaPolynomialLift_eval]
    exact predictionLocalPrimeGoodEvent_den_nonzero F (tests q) (den q) (hden q) w _ (hx q)
  have hfactor : ∀ᶠ w in atTop, ∀ _q : Fin b, (F.modulus w : ℕ) ∣ (F.modulus w : ℕ) :=
    Eventually.of_forall (fun _ _ => dvd_refl _)
  let num w := masterPredictionOriginalMajorantAverage (d := d) F C (fun w _ => label w) root
    (fun w j => globalGap w j) (fun w _ => (F.modulus w : ℕ)) f (fun _ _ _ => 0)
    (predictionVariableQuotientLength F gap J choice (fun w _ => (F.modulus w : ℕ)) f) E w
  let c : ℝ := 2 ^ Fintype.card (ReplicaCubeRow b d)
  have hm : Tendsto (fun w => num w - c * event
      (masterPrimeSlotsMass F w (fun j => globalGap w j)) (E w)) atTop (𝓝 0) :=
    hF.prediction_quotient_majorant_mean_tendsto C hN (fun w _ => label w) tail
      (htail.mono (fun _ hw _ => hw)) root gap globalGap J hJ choice htailroot htailgap
      htailprime polys hpolys (fun w _ => (F.modulus w : ℕ)) hfactor f hf (fun _ _ _ => 0)
      E hslots hnonzero
  have hnumEq (w : ℕ) : masterReplicaDualNumerator F root (fun _ => d) arity e gap J choice
      tests den H ε g w = num w := by
    unfold masterReplicaDualNumerator masterPredictionVariableWeightedCubeAverage num
      masterPredictionOriginalMajorantAverage conditionalFiniteAverage
    apply congrArg (expectation (masterPrimeSlotsMass F w (fun j => globalGap w j)))
    funext x
    split_ifs
    · have hG : predictionReplicaRowTests (H w) (g w) ((replicaPrimeSampleEquiv arity e) x) =
          (fun _ : VariableReplicaCubeRow (fun _ : Fin b => d) => H w) := by
        funext row
        cases row <;> rfl
      simp only [hG, ε, Finset.prod_const_one, one_mul]
      exact constant_cube_majorant_expectation _ _ _ _ (masterPredictionBlockMask F C label w)
    · rfl
  have hprobEq (w : ℕ) : event (masterPrimeSlotsMass F w (fun j => globalGap w j)) (E w) =
      ∏ q, event (masterReplicaLocalPrimeMass F arity gap w q)
        (predictionLocalPrimeGoodEvent F (tests q) (den q) w) := by
    rw [← expectation_indicator]
    have he := master_replica_prime_expectation arity e F w (gap w)
      (fun x => if ∀ q, predictionLocalPrimeGoodEvent F (tests q) (den q) w (x q) then 1 else 0)
    calc
      _ = expectation (masterPrimeSlotsMass F w (fun j => globalGap w j))
          (fun x => if ∀ q, predictionLocalPrimeGoodEvent F (tests q) (den q) w
            ((replicaPrimeSampleEquiv arity e) x q) then 1 else 0) := by
        apply congrArg (expectation (masterPrimeSlotsMass F w (fun j => globalGap w j)))
        funext x
        split_ifs <;> rfl
      _ = expectation (piMass (masterReplicaLocalPrimeMass F arity gap w))
          (fun x => if ∀ q, predictionLocalPrimeGoodEvent F (tests q) (den q) w (x q) then 1 else 0) := he
      _ = event (piMass (masterReplicaLocalPrimeMass F arity gap w))
          (fun x => ∀ q, predictionLocalPrimeGoodEvent F (tests q) (den q) w (x q)) := by
        rw [← expectation_indicator]
        apply congrArg (expectation (piMass (masterReplicaLocalPrimeMass F arity gap w)))
        funext x
        split_ifs <;> rfl
      _ = _ := event_piMass_all _ _
  have hevent (q : Fin b) : Tendsto (fun w => event (masterReplicaLocalPrimeMass F arity gap w q)
      (predictionLocalPrimeGoodEvent F (tests q) (den q) w)) atTop (𝓝 1) :=
    hF.local_prime_good_event_tendsto_one (tests q) (den q) (hden q) (masterSlot q)
      (hmasterSlot q) (fun p hp => hinclude q p hp) (fun w => gap w q)
  have hp : Tendsto (fun w => ∏ q, event (masterReplicaLocalPrimeMass F arity gap w q)
      (predictionLocalPrimeGoodEvent F (tests q) (den q) w)) atTop (𝓝 1) := by
    simpa only [Finset.prod_const_one] using tendsto_finsetProd Finset.univ (fun q _ => hevent q)
  have he : Tendsto (fun w => event (masterPrimeSlotsMass F w (fun j => globalGap w j)) (E w))
      atTop (𝓝 1) := by
    simpa only [hprobEq] using hp
  have hnum : Tendsto num atTop (𝓝 c) := by
    have hx := hm.add ((tendsto_const_nhds (x := c)).mul he)
    convert hx using 1 <;> simp
  have hz := hnum.div hp (by norm_num : (1 : ℝ) ≠ 0)
  convert hz using 1
  · funext w
    exact (master_replica_dual_normalized_formula F root (fun _ => d) arity e gap J choice
      tests den H ε g w).trans (congrArg
        (fun a => a / ∏ q, event (masterReplicaLocalPrimeMass F arity gap w q)
          (predictionLocalPrimeGoodEvent F (tests q) (den q) w)) (hnumEq w))
  · simp only [div_one, c, replicaCubeRow_card]

end Hindman168
