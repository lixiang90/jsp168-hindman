import Hindman168.MaskOriginalStagePrefactors
import Hindman168.MaskCopiedNormalizedMoments

/-! The original normalized good-prime/base joint probability and its
conditional independent direction pairs. Outside the retained prime event,
a unit point mass completes each direction law and changes no conditional
stage prefactor. The common m-only bound holds for all finite stages. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

namespace FiniteMass

theorem conditionMass_mem_support_event {α : Type*} (μ : Mass α) (E : α → Prop) (x : α)
    (hx : x ∈ (conditionMass μ E).support) : E x := by
  by_contra hn
  apply Finsupp.mem_support_iff.mp hx
  rw [conditionMass_apply, if_neg hn]

end FiniteMass

namespace MaskOriginalSampling

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

local notation "S" => maskOriginalSampling m gap a ha C hC t J hJ hgap

noncomputable def outsideMass (w : ℕ) :
    Mass ((Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) × (Fin (m + 1) → ℤ)) :=
  conditionalJoint (conditionMass ((S).primeMass w) (maskGeneratedCopiedPrimeGood m gap t w))
    (fun _ => maskOriginalBaseMass m gap C w)

noncomputable def completedDirectionMass (w : ℕ)
    (p : (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) × (Fin (m + 1) → ℤ))
    (k : (S).Direction) : Mass ℤ :=
  eventCompletedDirectionMass (maskGeneratedCopiedPrimeGood m gap t w)
    (fun x (_k : (S).Direction) => uniformIntervalMass 0 (maskGeneratedShiftLength m gap t J w x)) p.1 k

theorem outside_probability_eventually :
    ∀ᶠ w in atTop,
      (∀ p, 0 ≤ outsideMass gap a ha C hC t J hJ hgap w p) ∧
      total (outsideMass gap a ha C hC t J hJ hgap w) = 1 := by
  filter_upwards [(S).conditioned_prime_probability_eventually,
    base_probability_eventually gap C hC] with w hp hb
  unfold outsideMass
  refine ⟨conditionalJoint_nonneg _ _ hp.1 (fun _ _ => hb.1), ?_⟩
  rw [conditionalJoint_total]
  have he : (fun _x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ =>
      total (maskOriginalBaseMass m gap C w)) = fun _ => (1 : ℝ) :=
    funext (fun _ => hb.2)
  rw [he]
  have hc : expectation (conditionMass ((S).primeMass w)
      (maskGeneratedCopiedPrimeGood m gap t w)) (fun _ => 1) =
      total (conditionMass ((S).primeMass w) (maskGeneratedCopiedPrimeGood m gap t w)) := by
    simp only [expectation, total, Finsupp.sum, mul_one]
  exact hc.trans hp.2

theorem completed_direction_probability_eventually :
    ∀ᶠ w in atTop,
      (∀ p k z, 0 ≤ completedDirectionMass gap a ha C hC t J hJ hgap w p k z) ∧
      ∀ p k, total (completedDirectionMass gap a ha C hC t J hJ hgap w p k) = 1 := by
  filter_upwards [maskGeneratedShiftLength_eventually_pos m gap t J hJ] with w hw
  refine ⟨fun p k z => eventCompletedDirectionMass_nonneg
    (maskGeneratedCopiedPrimeGood m gap t w)
    (fun x (_k : (S).Direction) => uniformIntervalMass 0 (maskGeneratedShiftLength m gap t J w x))
    (fun _ _ _ z => uniformIntervalMass_nonneg _ _ z) p.1 k z, ?_⟩
  intro p k
  exact eventCompletedDirectionMass_total _ _
    (fun x hx _ => uniformIntervalMass_total 0 (hw x hx)) p.1 k

theorem normalizedStagePrefactor_eq_joint
    (label : ℕ → (S).BaseRow → Fin (m + 1)) (w : ℕ)
    (K : Finset (S).Direction) (base : (S).BaseRow) :
    (S).normalizedStagePrefactor label w K base =
      expectation (outsideMass gap a ha C hC t J hJ hgap w) (fun p =>
        expectation (piMass (fun k => tensor
          (completedDirectionMass gap a ha C hC t J hJ hgap w p k)
          (completedDirectionMass gap a ha C hC t J hJ hgap w p k)))
          (fun v => ∏ u ∈ (S).stageIndices K base,
            (1 + (S).weight ((S).labels label) (S).rows w u p.1
              (additiveSampleCoordinates p.2 v)))) := by
  unfold MaskCopiedSampling.normalizedStagePrefactor outsideMass
  rw [expectation_conditionalJoint]
  apply expectation_congr_support
  intro x hx
  have hxG := conditionMass_mem_support_event ((S).primeMass w)
    (maskGeneratedCopiedPrimeGood m gap t w) x hx
  have hb : piMass ((S).originalColumnMass w x) = maskOriginalBaseMass m gap C w := by
    apply congrArg piMass
    funext col
    exact originalColumnMass_eq gap a ha C hC t J hJ hgap w x col
  have hd (z : Fin (m + 1) → ℤ) :
      piMass (fun k => tensor ((S).directionMass w x k) ((S).directionMass w x k)) =
      piMass (fun k => tensor (completedDirectionMass gap a ha C hC t J hJ hgap w (x, z) k)
        (completedDirectionMass gap a ha C hC t J hJ hgap w (x, z) k)) := by
    apply congrArg piMass
    funext k
    have hk : (S).directionMass w x k = completedDirectionMass gap a ha C hC t J hJ hgap w (x, z) k := by
      exact (directionMass_eq gap a ha C hC t J hJ hgap w x k).trans (by
        unfold completedDirectionMass eventCompletedDirectionMass
        rw [if_pos hxG])
    exact congrArg₂ tensor hk hk
  apply congrArg₂ expectation hb
  funext z
  exact congrArg (fun μ => expectation μ (fun v => ∏ u ∈ (S).stageIndices K base,
    (1 + (S).weight ((S).labels label) (S).rows w u x (additiveSampleCoordinates z v)))) (hd z)

theorem all_normalizedStagePrefactors_eventually_le
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → (S).BaseRow → Fin (m + 1)) :
    ∀ᶠ w in atTop, ∀ K : Finset (S).Direction, ∀ base : (S).BaseRow,
      (S).normalizedStagePrefactor label w K base ≤ maskCopiedMajorantBound m := by
  apply eventually_all.mpr
  intro K
  apply eventually_all.mpr
  intro base
  apply (S).normalizedStagePrefactor_eventually_le label
    ((divisor_budget gap a ha C hC t J hJ hgap htail).mono (fun w hw base => hw (label w base)))
  · intro k bit
    exact maskOriginalHarmonic_not_inr m gap t (k, bit)
  · intro w x k bit; rfl
  · intro w x k bit; rfl

end MaskOriginalSampling
end Hindman168
