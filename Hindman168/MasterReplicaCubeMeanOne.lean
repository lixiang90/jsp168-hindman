import Hindman168.ReplicaCubePolynomialTests
import Hindman168.RoughDenominatorUnits

/-!
# Master mean-one for actual prediction replica cube subsystems

Replica moduli are smooth factors times rough parts of fixed polynomial
values. The anchor and distinguishing variable prove the row conditions;
they are not assumptions. The theorem applies to any injectively selected
subsystem, as required when expanding the prediction majorants. The base
law remains the actual mixture of harmonic variables and integer intervals.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def masterPredictionCubeCoefficient {r b d q : ℕ}
    (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (row : ℕ → Fin q → ReplicaCubeRow b d) (w : ℕ) (x : Fin r → ℕ)
    (u : Fin q) (j : Fin (Fintype.card (ReplicaCubeColumn b d))) : ℤ :=
  replicaCubeFinCoefficient (fun v => predictionCubeModulus w (s w v) (f v) x) (row w u) j

theorem masterPredictionCubeCoefficient_primitive {r b d q w p : ℕ} (hp : p.Prime)
    (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (row : ℕ → Fin q → ReplicaCubeRow b d) (x : Fin r → ℕ) (u : Fin q) :
    ∃ j, (masterPredictionCubeCoefficient s f row w x u j : ZMod p) ≠ 0 :=
  replicaCubeFinCoefficient_primitive hp _ _

theorem masterPredictionCubeCoefficient_pair_independent {r b d q w V : ℕ}
    (s : ℕ → Fin b → ℕ) (e : ℕ → Fin b → ℕ)
    (hs : ∀ v, s w v ∣ primorial w ^ e w v)
    (f : Fin b → MvPolynomial (Fin r) ℤ) (T : Finset (MvPolynomial (Fin r) ℤ))
    (hf : ∀ v, f v ∈ T) (row : ℕ → Fin q → ReplicaCubeRow b d)
    (hrow : Function.Injective (row w)) (x : Fin r → ℕ)
    (p : boundedRoughPrimeSet w V)
    (hbad : ¬ squarefreeCRTBadEvent (boundedRoughPrimeSet w V)
      (fun p hp => ((mem_boundedRoughPrimeSet w V p).mp hp).1) T
      (fun j => (x j : ZMod (squarefreeCRTModulus (boundedRoughPrimeSet w V)))) p)
    (u v : Fin q) (huv : u ≠ v) :
    LinearIndependent (ZMod (p : ℕ))
      ![(fun j => (masterPredictionCubeCoefficient s f row w x u j : ZMod (p : ℕ))),
        (fun j => (masterPredictionCubeCoefficient s f row w x v j : ZMod (p : ℕ)))] := by
  have hp := (mem_boundedRoughPrimeSet w V (p : ℕ)).mp p.property
  exact replicaCube_polynomial_pair_independent (boundedRoughPrimeSet w V)
    (fun p hp => ((mem_boundedRoughPrimeSet w V p).mp hp).1)
    T f hf (s w) x p
    (fun v => smooth_denominator_coprime (e w v) (hs v)
      (prime_coprime_primorial_of_gt hp.1 hp.2.1).symm)
    hbad (row w u) (row w v) (fun h => huv (hrow h))

theorem MasterParameterConditions.replica_cube_mean_one_tendsto
    {n N m q r b d L : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (label : ℕ → Fin q → Fin m)
    (gap : ℕ → Fin r → Fin L) (V : ℕ → ℕ) (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hdivbudget : ∀ᶠ w in atTop, ∀ u, tailBound ((C w).tailCutoffs (F.cutoff w) (label w u)) ≤ V w)
    (hprimebudget : ∀ᶠ w in atTop, ∀ j, V w ≤ F.auxiliary w (gap w j))
    (T : Finset (MvPolynomial (Fin r) ℤ)) (hT : ∀ f ∈ T, f ≠ 0)
    (s : ℕ → Fin b → ℕ) (e : ℕ → Fin b → ℕ)
    (hs : ∀ᶠ w in atTop, ∀ v, s w v ∣ primorial w ^ e w v)
    (f : Fin b → MvPolynomial (Fin r) ℤ) (hf : ∀ v, f v ∈ T)
    (row : ℕ → Fin q → ReplicaCubeRow b d)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w))
    (H : Finset (Fin (Fintype.card (ReplicaCubeColumn b d))))
    (index : ℕ → Fin (Fintype.card (ReplicaCubeColumn b d)) → Fin N)
    (Tmin : ℕ → Fin (Fintype.card (ReplicaCubeColumn b d)) → ℕ)
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (ReplicaCubeColumn b d)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (ReplicaCubeColumn b d)) → ℕ)
    (E : ℕ → (Fin r → ℕ) → Prop)
    (hharmbudget : ∀ᶠ w in atTop, ∀ j ∈ H, V w ≤ F.auxiliary w (index w j).val)
    (hlengthgrowth : ∀ j, j ∉ H → PowerDominates atTop (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)))
    (hlen : ∀ᶠ w in atTop, ∀ x, E w x → ∀ j, j ∉ H → Tmin w j ≤ len w x j) :
    Tendsto (fun w => masterChainWeightedMean F w (C w) (label w) (fun j => gap w j)
        (masterMixedBaseMass H F index loc len w)
        (masterPredictionCubeCoefficient s f row w) (E w) -
      event (masterPrimeSlotsMass F w (fun j => gap w j)) (E w)) atTop (𝓝 0) := by
  apply hF.chain_mixed_weighted_mean_one_tendsto C hN label gap V hV
    hdivbudget hprimebudget T hT H index Tmin loc len
    (masterPredictionCubeCoefficient s f row) E hharmbudget hlengthgrowth hlen
  · exact Eventually.of_forall (fun w x _ p u =>
      masterPredictionCubeCoefficient_primitive
        ((mem_boundedRoughPrimeSet w (V w) (p : ℕ)).mp p.property).1 s f row x u)
  · filter_upwards [hs, hrow] with w hsw hrw
    intro x _ p hbad u v huv
    exact masterPredictionCubeCoefficient_pair_independent s e hsw f T hf row hrw x p hbad u v huv

end Hindman168
