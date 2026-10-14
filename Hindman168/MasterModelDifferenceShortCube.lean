import Hindman168.MasterInverseShortCubeEstimate
import Hindman168.OriginalMasterSelectedModels
import Hindman168.MasterGapIndex

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Topology Classical
universe u

/-- The original model difference is an actual bounded Hilbert family.
The inverse input selects J and a positive threshold before the master
count and arithmetic data. Natural master indices retain their original
integer masses, polynomial steps and conditioned prime law. -/
theorem master_model_difference_shortCube_threshold (s d : ℕ)
    (hinverse : HasNativePeriodicIntervalInverse.{u} s (2 ^ d + 2 ^ d - 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∃ κ : ℝ, 0 < κ ∧
      ∀ {n M : ℕ} (hM : 0 < M)
        (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ p ∈ D, p ≠ 0)
        (pol : MvPolynomial (Fin n) ℤ) (_hpol : pol ∈ D)
        (T : Finset (MvPolynomial (Fin n) ℤ)) (_hT : ∀ p ∈ T, p ≠ 0) (_hpolT : pol ∈ T)
        (l i : ℕ) (_hl : l < M) (_hi : i < M) (_hli : l ≤ i),
      let F := constructedMasterFamily M D hD
      ∀ (U : Ultrafilter ℕ) (_hU : (U : Filter ℕ) ≤ atTop)
        (f t : boundedHilbertFamilies (fun w => FiniteMassL2 (originalPivotMass F i w)))
        (_hf : ∀ w y, 0 ≤ f.val w y ∧ f.val w y ≤ 1)
        (_ht : ∀ w y, 0 ≤ t.val w y ∧ t.val w y ≤ 1),
      ‖(nativeNilHilbertSubspace.{u} s F (originalPivotMass F i) U
        (masterGapIndex M hM l)).starProjection
          (hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U t)‖ < κ →
      ∀ᶠ w in (U : Filter ℕ),
        let μ := conditionMass (dyadicPoolTupleMass (fun _ : Fin n => F.pool w l))
          (primeSampleGood T)
        expectation μ (fun x => |integerPredictionShortCubeStatistic w (F.modulus w : ℕ)
          (F.gap w l) (F.cutoff w i) d J pol (fun y => f.val w y - t.val w y) x|) < ε := by
  obtain ⟨J, hJ, κ, hκ, he⟩ := master_inverse_shortCube_uniform_threshold s d hinverse ε hε
  refine ⟨J, hJ, κ, hκ, ?_⟩
  intro n M hM D hD pol hpol T hT hpolT l i hl hi hli F U hU f t hf ht hp
  let gap : ℕ → Fin M := fun _ => ⟨l, hl⟩
  let pivot : ℕ → Fin M := fun _ => ⟨i, hi⟩
  have hmap : masterGapIndex M hM l = gap := by
    funext w
    apply Fin.ext
    exact masterGapIndex_val M hM l w hl
  have hx := he D hD pol hpol T hT hpolT
    gap pivot (Eventually.of_forall (fun _ => hli))
  have hb : ∀ w y, |(f - t).val w y| ≤ 1 := by
    intro w y
    change |f.val w y - t.val w y| ≤ 1
    exact abs_le.mpr ⟨by linarith [(hf w y).1, (ht w y).2],
      by linarith [(hf w y).2, (ht w y).1]⟩
  have hs : hilbertFamilyToCompletion _ U (f - t) =
      hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U t :=
    (hilbertFamilyCompletionLinearMap _ U).map_sub f t
  exact hx U hU (f - t) hb (by rw [hs, ← hmap]; exact hp)

end Hindman168
