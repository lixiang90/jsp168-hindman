import Hindman168.MaskGeneratedCopiedMajorant

/-! The majorant bound depends only on the original column parameter m.
Actual sampling locations, lengths, templates and selected subsystems only
change the eventual threshold, not the constant. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem additiveCopy_card_le (b : ℕ) :
    Fintype.card (CopiedReplicaCubeRow (additiveRowAssigned b)) ≤ (b + 1) * 2 ^ b := by
  have ha : Fintype.card (Fin b × CubeVertex 1) = b := by
    have he := Fintype.card_congr (Equiv.ofBijective (additiveRowAssigned b)
      ⟨additiveRowAssigned_injective b, additiveRowAssigned_surjective b⟩)
    simpa only [Fintype.card_fin] using he.symm
  calc
    _ ≤ Fintype.card (ReplicaCubeRow b 1 × (Fin b → Bool)) := Fintype.card_subtype_le _
    _ = (b + 1) * 2 ^ b := by
      simp only [Fintype.card_prod, ReplicaCubeRow, Fintype.card_option,
        ha, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

theorem maskCopiedRow_card_le (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :
    Fintype.card (MaskCopiedRow m gap t) ≤ (maskRowCountBound m + 1) * 2 ^ maskRowCountBound m := by
  have h := maskGenerated_additive_dimension_le m gap t
  exact (additiveCopy_card_le _).trans (by gcongr; norm_num)

noncomputable def maskCopiedMajorantBound (m : ℕ) : ℝ :=
  ((2 ^ ((maskRowCountBound m + 1) * 2 ^ maskRowCountBound m) : ℕ) : ℝ) + 1

theorem maskCopiedMajorantBound_pos (m : ℕ) : 0 < maskCopiedMajorantBound m := by
  unfold maskCopiedMajorantBound
  positivity

namespace MaskCopiedSampling

variable {m N : ℕ}

set_option maxHeartbeats 1000000 in
theorem majorant_eventually_le_column_bound (S : MaskCopiedSampling m N) {q : ℕ}
    (label : ℕ → Fin q → Fin (m + 1)) (row : ℕ → Fin q → MaskCopiedRow m S.gap S.template)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w))
    (hdivbudget : ∀ᶠ w in atTop, ∀ u,
      tailBound ((S.chain w).tailCutoffs ((maskGeneratedMaster m S.gap).cutoff w) (label w u)) ≤ S.budget w)
    (U : Finset (Fin q)) :
    ∀ᶠ w in atTop, conditionalFiniteAverage (S.primeMass w) (S.baseMass w)
      (maskGeneratedCopiedPrimeGood m S.gap S.template w)
      (fun x y => ∏ u ∈ U, (1 + S.weight label row w u x y)) ≤ maskCopiedMajorantBound m := by
  have hq : q ≤ Fintype.card (MaskCopiedRow m S.gap S.template) := by
    obtain ⟨w, hw⟩ := hrow.exists
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (row w) hw
  have hU : U.card ≤ (maskRowCountBound m + 1) * 2 ^ maskRowCountBound m :=
    (Finset.card_le_univ U).trans (by
      simpa only [Fintype.card_fin] using hq.trans (maskCopiedRow_card_le m S.gap S.template))
  exact (S.majorant_eventually_le label row hrow hdivbudget U).mono (fun w hw => hw.trans (by
    unfold maskCopiedMajorantBound
    gcongr; norm_num))

set_option maxHeartbeats 1000000 in
theorem all_majorants_eventually_le_column_bound (S : MaskCopiedSampling m N) {q : ℕ}
    (label : ℕ → Fin q → Fin (m + 1)) (row : ℕ → Fin q → MaskCopiedRow m S.gap S.template)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w))
    (hdivbudget : ∀ᶠ w in atTop, ∀ u,
      tailBound ((S.chain w).tailCutoffs ((maskGeneratedMaster m S.gap).cutoff w) (label w u)) ≤ S.budget w) :
    ∀ᶠ w in atTop, ∀ U : Finset (Fin q),
      conditionalFiniteAverage (S.primeMass w) (S.baseMass w)
        (maskGeneratedCopiedPrimeGood m S.gap S.template w)
        (fun x y => ∏ u ∈ U, (1 + S.weight label row w u x y)) ≤ maskCopiedMajorantBound m := by
  apply eventually_all.mpr
  intro U
  exact S.majorant_eventually_le_column_bound label row hrow hdivbudget U

end MaskCopiedSampling
end Hindman168
