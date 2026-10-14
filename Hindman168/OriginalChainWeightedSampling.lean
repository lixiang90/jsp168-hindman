import Hindman168.MasterChainSampling
import Hindman168.FiniteProductDensityLaw
import Hindman168.UnitCRTJointLaw

/-! The complete original raw-coordinate law approximates the weighted
original pivot product law uniformly over all unit-bounded joint tests. -/

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Topology Classical

theorem chain_comparison_coordinate_list {m : ℕ} (C : Chain m)
    (X : ℕ → ℕ) (W : ℕ) :
    (piMass (fun col => blockComparison W (C.cutoffs X col))).mapDomain List.ofFn =
      jointComparison W (List.ofFn (C.cutoffs X)) := by
  rw [piMass_ofFn]
  have hm : List.ofFn (fun col => blockComparison W (C.cutoffs X col)) =
      (List.ofFn (C.cutoffs X)).map (blockComparison W) :=
    List.ofFn_comp' (C.cutoffs X) (blockComparison W)
  rw [hm]
  rfl

theorem chain_integer_comparison_expectation {m : ℕ} (C : Chain m)
    (F : MasterParameterFamily) (w : ℕ) (f : (Fin m → ℤ) → ℝ) :
    expectation (piMass (fun col => integerProductComparisonMass
      (tailMass (primorial w) (C.tailCutoffs (F.cutoff w) col))
      (F.cutoff w (C.pivot col)) (primorial w))) f =
    expectation (piMass (fun col => integerMass (F.cutoff w (C.pivot col)) (primorial w)))
      (fun z => (∏ col, integerDivisorMask
        (tailMass (primorial w) (C.tailCutoffs (F.cutoff w) col)) (z col)) * f z) :=
  expectation_piMass_density _ _ _ (fun _ _ => integerProductComparisonMass_apply _ _ _ _) f

theorem MasterParameterConditions.chain_coordinate_distance_tendsto {n N m : ℕ}
    {A : Finset ℚ} {P : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A P F) (C : ℕ → Chain m)
    (hN : ∀ w col, (C w).block col ⊆ Finset.range N) :
    Tendsto (fun w => distance
      ((globalRawMass (F.cutoff w) (primorial w) N).mapDomain ((C w).sampleProducts (hN w)))
      (piMass (fun col => blockComparison (primorial w) ((C w).cutoffs (F.cutoff w) col))))
      atTop (𝓝 0) := by
  have hr := hF.chain_joint_rapid C hN (V := fun _ => 1)
    (Eventually.of_forall (fun _ => le_rfl))
    (Eventually.of_forall (fun w col => by
      have h := F.auxiliary_ge_two w ((C w).pivot col)
      omega))
  have he (w : ℕ) : distance
      ((globalRawMass (F.cutoff w) (primorial w) N).mapDomain ((C w).sampleProducts (hN w)))
      (piMass (fun col => blockComparison (primorial w) ((C w).cutoffs (F.cutoff w) col))) =
      distance ((globalRawMass (F.cutoff w) (primorial w) N).mapDomain
        (fun x => List.ofFn ((C w).sampleProducts (hN w) x)))
        (jointComparison (primorial w) (List.ofFn ((C w).cutoffs (F.cutoff w)))) := by
    rw [← distance_push_injective (List.ofFn_injective (n := m)),
      ← Finsupp.mapDomain_comp, chain_comparison_coordinate_list]
    rfl
  simp_rw [he]
  apply (Asymptotics.isLittleO_one_iff ℝ).mp
  simpa only [pow_zero, inv_one] using hr 0

theorem MasterParameterConditions.chain_weighted_testing_uniform {n N m : ℕ}
    {A : Finset ℚ} {P : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A P F) (C : ℕ → Chain m)
    (hN : ∀ w col, (C w).block col ⊆ Finset.range N) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ w in atTop, ∀ f : (Fin m → ℤ) → ℝ, (∀ z, |f z| ≤ 1) →
      |expectation (globalRawMass (F.cutoff w) (primorial w) N)
          (fun x => f (fun col => ((C w).sampleProducts (hN w) x col : ℤ))) -
        expectation (piMass (fun col => integerMass (F.cutoff w ((C w).pivot col)) (primorial w)))
          (fun z => (∏ col, integerDivisorMask
            (tailMass (primorial w) ((C w).tailCutoffs (F.cutoff w) col)) (z col)) * f z)| < η := by
  have ht := (hF.chain_coordinate_distance_tendsto C hN).eventually (Iio_mem_nhds hη)
  filter_upwards [ht] with w hw
  intro f hf
  rw [← chain_integer_comparison_expectation (C w) F w f]
  have h := expectation_difference_bound
    ((globalRawMass (F.cutoff w) (primorial w) N).mapDomain ((C w).sampleProducts (hN w)))
    (piMass (fun col => blockComparison (primorial w) ((C w).cutoffs (F.cutoff w) col)))
    (fun z => f (fun col => (z col : ℤ))) 1 (fun z => hf _)
  have hc := congrArg (fun μ : Mass (Fin m → ℤ) => expectation μ f)
    (piMass_map (fun col => blockComparison (primorial w) ((C w).cutoffs (F.cutoff w) col))
      (fun _ (y : ℕ) => (y : ℤ)))
  rw [expectation_push] at hc
  rw [expectation_push, hc] at h
  exact h.trans_lt (by simpa only [one_mul] using hw)

end Hindman168
