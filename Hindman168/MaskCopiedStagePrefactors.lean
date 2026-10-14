import Hindman168.MaskCopiedUniformBounds
import Hindman168.AdditiveRowSamplingLaw

/-! The actual assigned stage prefactor is a subset majorant under the same
original coordinate and conditional independent pair laws. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def additiveCopyEnumeration (b : ℕ) :
    Fin (Fintype.card (CopiedReplicaCubeRow (additiveRowAssigned b))) →
      CopiedReplicaCubeRow (additiveRowAssigned b) :=
  (Fintype.equivFin (CopiedReplicaCubeRow (additiveRowAssigned b))).symm

noncomputable def additiveStageRowIndices (b : ℕ) (K : Finset (Fin b)) (base : ReplicaCubeRow b 1) :
    Finset (Fin (Fintype.card (CopiedReplicaCubeRow (additiveRowAssigned b)))) :=
  Finset.univ.filter (fun u => additiveCopyEnumeration b u ∈
    predictionStageRowCopies (additiveRowAssigned b) K base)

namespace AdditiveRowData

variable {b c : ℕ}

theorem stageFactorProduct_enumerated (D : AdditiveRowData b c) (K : Finset (Fin b))
    (base : ReplicaCubeRow b 1) (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ) (f : ℤ → ℝ) :
    D.stageFactorProduct K base z (predictionPairValues v) f =
      ∏ u ∈ additiveStageRowIndices b K base,
        f (D.translatedForm (additiveCopyEnumeration b u).val.1
          (additiveCopyEnumeration b u).val.2 z (predictionPairValues v)) := by
  rw [D.stageFactorProduct_eq_prod]
  refine Finset.prod_bij
    (s := predictionStageRowCopies (additiveRowAssigned b) K base)
    (t := additiveStageRowIndices b K base)
    (f := fun r => f (D.translatedForm r.val.1 r.val.2 z (predictionPairValues v)))
    (g := fun u => f (D.translatedForm (additiveCopyEnumeration b u).val.1
      (additiveCopyEnumeration b u).val.2 z (predictionPairValues v)))
    (fun r _ => Fintype.equivFin (CopiedReplicaCubeRow (additiveRowAssigned b)) r) ?_ ?_ ?_ ?_
  · intro r hr
    simp only [additiveStageRowIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      additiveCopyEnumeration, Equiv.symm_apply_apply]
    exact hr
  · intro r _ s _ he
    exact (Fintype.equivFin (CopiedReplicaCubeRow (additiveRowAssigned b))).injective he
  · intro u hu
    refine ⟨additiveCopyEnumeration b u, (Finset.mem_filter.mp hu).2, ?_⟩
    exact (Fintype.equivFin (CopiedReplicaCubeRow (additiveRowAssigned b))).apply_symm_apply u
  · intro r _
    simp only [additiveCopyEnumeration, Equiv.symm_apply_apply]

end AdditiveRowData

namespace MaskCopiedSampling

variable {m N : ℕ}

abbrev BaseRow (S : MaskCopiedSampling m N) :=
  ReplicaCubeRow (Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m S.gap S.template).target)) 1

abbrev Direction (S : MaskCopiedSampling m N) :=
  Fin (Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m S.gap S.template).target))

noncomputable def columnIndex (S : MaskCopiedSampling m N)
    (col : PolynomialRowFamily.AdditiveColumn (maskGeneratedRowDataFamily m S.gap S.template).target m) :
    MaskCopiedIndex m S.gap S.template := Fintype.equivFin _ col

noncomputable def originalColumnMass (S : MaskCopiedSampling m N) (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m S.gap S.template).arity → ℕ) (col : Fin (m + 1)) : Mass ℤ :=
  let j := S.columnIndex (.inl col)
  if j ∈ S.harmonic then
    integerMass ((maskGeneratedMaster m S.gap).cutoff w (S.index w j).val) (primorial w)
  else uniformIntervalMass (S.location w x j) (S.length w x j)

noncomputable def directionMass (S : MaskCopiedSampling m N) (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m S.gap S.template).arity → ℕ) (k : S.Direction) : Mass ℤ :=
  uniformIntervalMass (S.location w x (S.columnIndex (.inr (k, false))))
    (S.length w x (S.columnIndex (.inr (k, false))))

theorem component_mass_eq (S : MaskCopiedSampling m N) (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m S.gap S.template).arity → ℕ)
    (haux : ∀ k bit, S.columnIndex (.inr (k, bit)) ∉ S.harmonic)
    (hloc : ∀ k bit, S.location w x (S.columnIndex (.inr (k, bit))) =
      S.location w x (S.columnIndex (.inr (k, false))))
    (hlen : ∀ k bit, S.length w x (S.columnIndex (.inr (k, bit))) =
      S.length w x (S.columnIndex (.inr (k, false)))) :
    S.baseMass w x = piMass (fun j => additiveComponentMass (S.originalColumnMass w x)
      (S.directionMass w x) ((Fintype.equivFin
        (PolynomialRowFamily.AdditiveColumn (maskGeneratedRowDataFamily m S.gap S.template).target m)).symm j)) := by
  have hp (col : PolynomialRowFamily.AdditiveColumn (maskGeneratedRowDataFamily m S.gap S.template).target m) :
      additiveComponentMass (S.originalColumnMass w x) (S.directionMass w x) col =
      if S.columnIndex col ∈ S.harmonic then
        integerMass ((maskGeneratedMaster m S.gap).cutoff w (S.index w (S.columnIndex col)).val) (primorial w)
      else uniformIntervalMass (S.location w x (S.columnIndex col)) (S.length w x (S.columnIndex col)) := by
    cases col with
    | inl j => rfl
    | inr kb =>
      rcases kb with ⟨k, bit⟩
      simp only [additiveComponentMass, Sum.elim_inr, directionMass,
        if_neg (haux k bit), hloc k bit, hlen k bit]
  unfold baseMass masterMixedBaseMass mixedIntegerBaseMass
  congr 1
  funext j
  rw [hp]
  simp only [columnIndex, Equiv.apply_symm_apply]

theorem sampling_law (S : MaskCopiedSampling m N) (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m S.gap S.template).arity → ℕ)
    (haux : ∀ k bit, S.columnIndex (.inr (k, bit)) ∉ S.harmonic)
    (hloc : ∀ k bit, S.location w x (S.columnIndex (.inr (k, bit))) =
      S.location w x (S.columnIndex (.inr (k, false))))
    (hlen : ∀ k bit, S.length w x (S.columnIndex (.inr (k, bit))) =
      S.length w x (S.columnIndex (.inr (k, false))))
    (f : (MaskCopiedIndex m S.gap S.template → ℤ) → ℝ) :
    expectation (S.baseMass w x) f =
      expectation (piMass (S.originalColumnMass w x)) (fun z =>
        expectation (piMass (fun k => tensor (S.directionMass w x k) (S.directionMass w x k)))
          (fun v => f (additiveSampleCoordinates z v))) := by
  rw [S.component_mass_eq w x haux hloc hlen]
  exact additiveSampleCoordinates_law _ _ f

noncomputable def rows (S : MaskCopiedSampling m N)
    (_ : ℕ) (u : Fin (Fintype.card (MaskCopiedRow m S.gap S.template))) : MaskCopiedRow m S.gap S.template :=
  (Fintype.equivFin (MaskCopiedRow m S.gap S.template)).symm u

noncomputable def labels (S : MaskCopiedSampling m N) (label : ℕ → S.BaseRow → Fin (m + 1))
    (w : ℕ) (u : Fin (Fintype.card (MaskCopiedRow m S.gap S.template))) : Fin (m + 1) :=
  label w (S.rows w u).val.1

noncomputable def stageIndices (S : MaskCopiedSampling m N) (K : Finset S.Direction) (base : S.BaseRow) :
    Finset (Fin (Fintype.card (MaskCopiedRow m S.gap S.template))) :=
  Finset.univ.filter (fun u => S.rows 0 u ∈ predictionStageRowCopies
    (additiveRowAssigned (Fintype.card (PolynomialRowFamily.OffTargetRow
      (maskGeneratedRowDataFamily m S.gap S.template).target))) K base)

noncomputable def stagePrefactor (S : MaskCopiedSampling m N) (label : ℕ → S.BaseRow → Fin (m + 1))
    (w : ℕ) (K : Finset S.Direction) (base : S.BaseRow) : ℝ :=
  conditionalFiniteAverage (S.primeMass w) (fun x => piMass (S.originalColumnMass w x))
    (maskGeneratedCopiedPrimeGood m S.gap S.template w) (fun x z =>
      expectation (piMass (fun k => tensor (S.directionMass w x k) (S.directionMass w x k)))
        (fun v => ∏ u ∈ S.stageIndices K base,
          (1 + S.weight (S.labels label) S.rows w u x (additiveSampleCoordinates z v))))

theorem stage_product_identification (S : MaskCopiedSampling m N)
    (label : ℕ → S.BaseRow → Fin (m + 1)) (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m S.gap S.template).arity → ℕ)
    (H : (maskGeneratedRowDataFamily m S.gap S.template).rows.AdditiveEliminationConditions
      (maskGeneratedMaster m S.gap) w (masterColumnCoefficient N S.a (fun w => (S.chain w).block) w)
      x (maskGeneratedRowDataFamily m S.gap S.template).target)
    (K : Finset S.Direction) (base : S.BaseRow) (z : Fin (m + 1) → ℤ) (v : S.Direction → ℤ × ℤ) :
    H.data.stageFactorProduct K base z (predictionPairValues v)
      (fun y => 1 + integerDivisorMask (tailMass (primorial w)
        ((S.chain w).tailCutoffs ((maskGeneratedMaster m S.gap).cutoff w) (label w base))) y) =
      ∏ u ∈ S.stageIndices K base,
        (1 + S.weight (S.labels label) S.rows w u x (additiveSampleCoordinates z v)) := by
  rw [H.data.stageFactorProduct_enumerated]
  apply Finset.prod_congr (by ext u; rfl)
  intro u hu
  have hb : (S.rows w u).val.1 = base :=
    ((mem_predictionStageRowCopies (additiveRowAssigned _) K base (S.rows w u)).mp
      (Finset.mem_filter.mp hu).2).2
  have hl : S.labels label w u = label w base := congrArg (label w) hb
  have he : (∑ j, S.coefficient S.rows w x u j * additiveSampleCoordinates z v j) =
      H.data.translatedForm (S.rows w u).val.1 (S.rows w u).val.2 z (predictionPairValues v) := by
    apply Eq.trans ?_ (additiveSampleCoordinates_eval H.data (S.rows w u) z v)
    apply Finset.sum_congr (by ext j; constructor <;> intro _ <;> exact Finset.mem_univ j)
    intro j _
    rw [H.copiedFinCoefficient_eq]
    rfl
  change (1 + integerDivisorMask (tailMass (primorial w)
    ((S.chain w).tailCutoffs ((maskGeneratedMaster m S.gap).cutoff w) (label w base)))
    (H.data.translatedForm (S.rows w u).val.1 (S.rows w u).val.2 z (predictionPairValues v))) = _
  unfold weight
  rw [hl, he]

theorem actual_stage_products_identified (S : MaskCopiedSampling m N)
    (label : ℕ → S.BaseRow → Fin (m + 1)) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m S.gap S.template w x →
      ∃ H : (maskGeneratedRowDataFamily m S.gap S.template).rows.AdditiveEliminationConditions
        (maskGeneratedMaster m S.gap) w (masterColumnCoefficient N S.a (fun w => (S.chain w).block) w)
        x (maskGeneratedRowDataFamily m S.gap S.template).target,
      ∀ K base z v, H.data.stageFactorProduct K base z (predictionPairValues v)
        (fun y => 1 + integerDivisorMask (tailMass (primorial w)
          ((S.chain w).tailCutoffs ((maskGeneratedMaster m S.gap).cutoff w) (label w base))) y) =
          ∏ u ∈ S.stageIndices K base,
            (1 + S.weight (S.labels label) S.rows w u x (additiveSampleCoordinates z v)) := by
  filter_upwards [maskGenerated_additive_elimination_data m S.gap S.a S.positive S.chain S.blocks] with w hw
  intro x hx
  obtain ⟨H⟩ := hw S.template x hx.2
  exact ⟨H, fun K base z v => S.stage_product_identification label w x H K base z v⟩

theorem stagePrefactor_eq (S : MaskCopiedSampling m N) (label : ℕ → S.BaseRow → Fin (m + 1))
    (haux : ∀ k bit, S.columnIndex (.inr (k, bit)) ∉ S.harmonic)
    (hloc : ∀ w x k bit, S.location w x (S.columnIndex (.inr (k, bit))) =
      S.location w x (S.columnIndex (.inr (k, false))))
    (hlen : ∀ w x k bit, S.length w x (S.columnIndex (.inr (k, bit))) =
      S.length w x (S.columnIndex (.inr (k, false))))
    (w : ℕ) (K : Finset S.Direction) (base : S.BaseRow) :
    S.stagePrefactor label w K base = conditionalFiniteAverage (S.primeMass w) (S.baseMass w)
      (maskGeneratedCopiedPrimeGood m S.gap S.template w)
      (fun x y => ∏ u ∈ S.stageIndices K base, (1 + S.weight (S.labels label) S.rows w u x y)) := by
  unfold stagePrefactor conditionalFiniteAverage
  apply congrArg (expectation (S.primeMass w))
  funext x
  split_ifs
  · exact (S.sampling_law w x haux (hloc w x) (hlen w x)
      (fun y => ∏ u ∈ S.stageIndices K base,
        (1 + S.weight (S.labels label) S.rows w u x y))).symm
  · rfl

theorem stagePrefactor_eventually_le (S : MaskCopiedSampling m N) (label : ℕ → S.BaseRow → Fin (m + 1))
    (hdivbudget : ∀ᶠ w in atTop, ∀ base,
      tailBound ((S.chain w).tailCutoffs ((maskGeneratedMaster m S.gap).cutoff w) (label w base)) ≤ S.budget w)
    (haux : ∀ k bit, S.columnIndex (.inr (k, bit)) ∉ S.harmonic)
    (hloc : ∀ w x k bit, S.location w x (S.columnIndex (.inr (k, bit))) =
      S.location w x (S.columnIndex (.inr (k, false))))
    (hlen : ∀ w x k bit, S.length w x (S.columnIndex (.inr (k, bit))) =
      S.length w x (S.columnIndex (.inr (k, false))))
    (K : Finset S.Direction) (base : S.BaseRow) :
    ∀ᶠ w in atTop, S.stagePrefactor label w K base ≤ maskCopiedMajorantBound m := by
  have h := S.majorant_eventually_le_column_bound (S.labels label) S.rows
    (Eventually.of_forall (fun _ => (Fintype.equivFin (MaskCopiedRow m S.gap S.template)).symm.injective))
    (hdivbudget.mono (fun w hw u => hw (S.rows w u).val.1)) (S.stageIndices K base)
  simpa only [S.stagePrefactor_eq label haux hloc hlen] using h

end MaskCopiedSampling
end Hindman168
