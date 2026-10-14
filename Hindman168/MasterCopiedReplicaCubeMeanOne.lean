import Hindman168.CopiedReplicaCubeRows
import Hindman168.MasterReplicaCubeMeanOne

/-!
# Actual master mean-one for duplicated prediction cube rows

Canonical copies avoid repeated zero-response branches. Their primitive
and pairwise independent row conditions are proved from the fixed direction
threshold, actual smooth factors and the original fixed polynomial tests.
All original divisor, prime-only event and mixed base laws are retained.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def masterCopiedPredictionCubeCoefficient {r b d h q : ℕ}
    (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (row : ℕ → Fin q → CopiedReplicaCubeRow dir)
    (w : ℕ) (x : Fin r → ℕ) (u : Fin q)
    (j : Fin (Fintype.card (CopiedReplicaCubeColumn b d h))) : ℤ :=
  copiedReplicaCubeFinCoefficient (fun v => predictionCubeModulus w (s w v) (f v) x) dir (row w u) j

theorem masterCopiedPredictionCubeCoefficient_primitive {r b d h q w p : ℕ} (hp : p.Prime)
    (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (row : ℕ → Fin q → CopiedReplicaCubeRow dir)
    (x : Fin r → ℕ) (u : Fin q) :
    ∃ j, (masterCopiedPredictionCubeCoefficient s f dir row w x u j : ZMod p) ≠ 0 :=
  copiedReplicaCubeFinCoefficient_primitive hp _ dir _

theorem masterCopiedPredictionCubeCoefficient_pair_independent {r b d h q w V : ℕ}
    (s : ℕ → Fin b → ℕ) (e : ℕ → Fin b → ℕ)
    (hs : ∀ v, s w v ∣ primorial w ^ e w v)
    (f : Fin b → MvPolynomial (Fin r) ℤ) (T : Finset (MvPolynomial (Fin r) ℤ))
    (hf : ∀ v, f v ∈ T) (dir : Fin h → Fin b × CubeVertex d)
    (hbound : replicaCubeResponseBound dir ≤ w)
    (row : ℕ → Fin q → CopiedReplicaCubeRow dir) (hrow : Function.Injective (row w))
    (x : Fin r → ℕ) (p : boundedRoughPrimeSet w V)
    (hbad : ¬ squarefreeCRTBadEvent (boundedRoughPrimeSet w V)
      (fun p hp => ((mem_boundedRoughPrimeSet w V p).mp hp).1) T
      (fun j => (x j : ZMod (squarefreeCRTModulus (boundedRoughPrimeSet w V)))) p)
    (u v : Fin q) (huv : u ≠ v) :
    LinearIndependent (ZMod (p : ℕ))
      ![(fun j => (masterCopiedPredictionCubeCoefficient s f dir row w x u j : ZMod (p : ℕ))),
        (fun j => (masterCopiedPredictionCubeCoefficient s f dir row w x v j : ZMod (p : ℕ)))] := by
  have hp := (mem_boundedRoughPrimeSet w V (p : ℕ)).mp p.property
  apply copiedReplicaCubeFinCoefficient_pair_independent hp.1 _ _ dir _
    (row w u) (row w v) (fun he => huv (hrow he))
  · intro v
    exact predictionCubeModulus_mod_nonzero hp.1
      (smooth_denominator_coprime (e w v) (hs v)
        (prime_coprime_primorial_of_gt hp.1 hp.2.1).symm)
      (f v) x (polynomial_nonzero_of_not_squarefree_bad _ _ T x p hbad (f v) (hf v))
  · intro i r hr
    exact replicaCubeResponseConstant_mod_nonzero dir hbound hp.2.1 i r hr

theorem MasterParameterConditions.copied_replica_cube_mean_one_tendsto
    {n N m q r b d h L : ℕ}
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
    (dir : Fin h → Fin b × CubeVertex d)
    (row : ℕ → Fin q → CopiedReplicaCubeRow dir)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w))
    (H : Finset (Fin (Fintype.card (CopiedReplicaCubeColumn b d h))))
    (index : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → Fin N)
    (Tmin : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (E : ℕ → (Fin r → ℕ) → Prop)
    (hharmbudget : ∀ᶠ w in atTop, ∀ j ∈ H, V w ≤ F.auxiliary w (index w j).val)
    (hlengthgrowth : ∀ j, j ∉ H → PowerDominates atTop (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)))
    (hlen : ∀ᶠ w in atTop, ∀ x, E w x → ∀ j, j ∉ H → Tmin w j ≤ len w x j) :
    Tendsto (fun w => masterChainWeightedMean F w (C w) (label w) (fun j => gap w j)
        (masterMixedBaseMass H F index loc len w)
        (masterCopiedPredictionCubeCoefficient s f dir row w) (E w) -
      event (masterPrimeSlotsMass F w (fun j => gap w j)) (E w)) atTop (𝓝 0) := by
  apply hF.chain_mixed_weighted_mean_one_tendsto C hN label gap V hV
    hdivbudget hprimebudget T hT H index Tmin loc len
    (masterCopiedPredictionCubeCoefficient s f dir row) E hharmbudget hlengthgrowth hlen
  · exact Eventually.of_forall (fun w x _ p u =>
      masterCopiedPredictionCubeCoefficient_primitive
        ((mem_boundedRoughPrimeSet w (V w) (p : ℕ)).mp p.property).1 s f dir row x u)
  · filter_upwards [hs, hrow, eventually_ge_atTop (replicaCubeResponseBound dir)] with w hsw hrw hbw
    intro x _ p hbad u v huv
    exact masterCopiedPredictionCubeCoefficient_pair_independent s e hsw f T hf dir hbw row hrw x p hbad u v huv

end Hindman168
