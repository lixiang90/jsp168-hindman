import Hindman168.AdditiveRowTerminalProducts
import Hindman168.UniformIntervals

/-!
The actual mask rows supply general elimination data with no assumed zero
response. The recurrence uses arbitrary original nonnegative outside masses
and conditional interval laws; no new probability law is inferred.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

namespace PolynomialRowFamily

abbrev OffTargetRow {r : ℕ} (target : Fin r) := {i : Fin r // i ≠ target}

noncomputable def additiveIndexEquiv {r : ℕ} (target : Fin r) :
    ReplicaCubeRow (Fintype.card (OffTargetRow target)) 1 ≃ Fin r := by
  let e := Fintype.equivFin (OffTargetRow target)
  refine {
    toFun := fun base => match base with | none => target | some p => (e.symm p.1).val
    invFun := fun i => if h : i = target then none else some (additiveRowAssigned _ (e ⟨i, h⟩))
    left_inv := ?_
    right_inv := ?_ }
  · intro base
    cases base with
    | none => simp
    | some p =>
      have hn := (e.symm p.1).property
      simp only [dif_neg hn]
      change some (additiveRowAssigned _ (e (e.symm p.1))) = some p
      rw [e.apply_symm_apply]
      obtain ⟨k, hk⟩ := additiveRowAssigned_surjective (Fintype.card (OffTargetRow target)) p
      have he : k = p.1 := congrArg Prod.fst hk
      exact congrArg some (he ▸ hk)
  · intro i
    by_cases hi : i = target
    · subst i
      simp
    · simp only [dif_neg hi, additiveRowAssigned, Equiv.symm_apply_apply]

theorem additiveIndexEquiv_root {r : ℕ} (target : Fin r) : additiveIndexEquiv target none = target := rfl

theorem additiveIndexEquiv_assigned_ne {r : ℕ} (target : Fin r)
    (k : Fin (Fintype.card (OffTargetRow target))) :
    additiveIndexEquiv target (some (additiveRowAssigned _ k)) ≠ target := by
  intro he
  have h := (additiveIndexEquiv target).injective (he.trans (additiveIndexEquiv_root target).symm)
  exact Option.some_ne_none _ h

theorem offTargetRow_card {r : ℕ} (target : Fin r) :
    Fintype.card (OffTargetRow target) = r - 1 := by
  change Fintype.card {i : Fin r // ¬ i = target} = r - 1
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]

noncomputable def integerAdditiveRowData {n r m W : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ) (x : Fin n → ℕ) (target : Fin r)
    (hrows : F.NormalizedIntegerRowConditions x c W)
    (htrans : F.IntegerTranslationConditions master w c x target) :
    AdditiveRowData (Fintype.card (OffTargetRow target)) (m + 1) where
  coefficient := fun i => F.normalizedIntegerRow x c (additiveIndexEquiv target i)
  direction := fun k => F.integerTranslation master w c x target
    (additiveIndexEquiv target (some (additiveRowAssigned _ k)))
  annihilate := fun k => by
    have he := (hrows.form_cast (additiveIndexEquiv target (some (additiveRowAssigned _ k)))
      (F.integerTranslation master w c x target (additiveIndexEquiv target (some (additiveRowAssigned _ k))))).trans
      (htrans.fixed_response _ (additiveIndexEquiv_assigned_ne target k))
    exact_mod_cast he

theorem integerAdditiveRowData_form {n r m W : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ) (x : Fin n → ℕ) (target : Fin r)
    (hrows : F.NormalizedIntegerRowConditions x c W)
    (htrans : F.IntegerTranslationConditions master w c x target)
    (i : ReplicaCubeRow (Fintype.card (OffTargetRow target)) 1) (z : Fin (m + 1) → ℤ) :
    (F.integerAdditiveRowData master w c x target hrows htrans).form i z =
      F.normalizedIntegerLinearForm x c (additiveIndexEquiv target i) z := rfl

theorem integerAdditiveRowData_target_response {n r m W : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ) (x : Fin n → ℕ) (target : Fin r)
    (hrows : F.NormalizedIntegerRowConditions x c W)
    (htrans : F.IntegerTranslationConditions master w c x target)
    (k : Fin (Fintype.card (OffTargetRow target))) :
    (F.integerAdditiveRowData master w c x target hrows htrans).response none k =
      (F.translationModulus master w x target : ℤ) := by
  have he := (hrows.form_cast target
    (F.integerTranslation master w c x target (additiveIndexEquiv target (some (additiveRowAssigned _ k))))).trans
    (htrans.target_response _ (additiveIndexEquiv_assigned_ne target k))
  exact_mod_cast he

structure AdditiveEliminationConditions {n r m : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ) (x : Fin n → ℕ) (target : Fin r) where
  data : AdditiveRowData (Fintype.card (OffTargetRow target)) (m + 1)
  form_eq : ∀ i z, data.form i z = F.normalizedIntegerLinearForm x c (additiveIndexEquiv target i) z
  direction_eq : ∀ k j, data.direction k j = F.integerTranslation master w c x target
    (additiveIndexEquiv target (some (additiveRowAssigned _ k))) j
  target_response : ∀ k, data.response none k = (F.translationModulus master w x target : ℤ)

end PolynomialRowFamily

theorem maskGenerated_additive_elimination_data (m : ℕ) {N : ℕ}
    (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ k, 0 < a k)
    (C : ℕ → Chain (m + 1)) (hC : ∀ w k, (C w).block k ⊆ Finset.range N) :
    ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)), ∀ x,
      predictionLocalPrimeGoodEvent (maskGeneratedMaster m gap)
        ((maskGeneratedRowDataFamily m gap t).rows.catalog (maskGeneratedRowDataFamily m gap t).target)
        ((maskGeneratedRowDataFamily m gap t).rows.denominator (maskGeneratedRowDataFamily m gap t).target) w x →
      Nonempty ((maskGeneratedRowDataFamily m gap t).rows.AdditiveEliminationConditions
        (maskGeneratedMaster m gap) w (masterColumnCoefficient N a (fun w => (C w).block) w) x
        (maskGeneratedRowDataFamily m gap t).target) := by
  filter_upwards [maskGenerated_chain_integer_row_conditions m gap a ha C hC,
    maskGenerated_integer_translation_conditions m gap a ha (fun w => (C w).block) hC
      (fun w k => (C w).block_nonempty k)] with w hr ht
  intro t x hg
  let F := (maskGeneratedRowDataFamily m gap t).rows
  let target := (maskGeneratedRowDataFamily m gap t).target
  let c := masterColumnCoefficient N a (fun w => (C w).block) w
  have hrows := hr t x
  have htrans := ht t x hg
  exact ⟨{
    data := F.integerAdditiveRowData (maskGeneratedMaster m gap) w c x target hrows htrans
    form_eq := F.integerAdditiveRowData_form (maskGeneratedMaster m gap) w c x target hrows htrans
    direction_eq := fun _ _ => rfl
    target_response := F.integerAdditiveRowData_target_response (maskGeneratedMaster m gap) w c x target hrows htrans }⟩

theorem maskGenerated_additive_dimension_le (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :
    Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target) ≤
      maskRowCountBound m := by
  rw [PolynomialRowFamily.offTargetRow_card]
  exact maskGeneratedRowDataFamily_dimension_le m gap t

theorem maskGenerated_additive_elimination_family {α : Type*} (m : ℕ) {N : ℕ}
    (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ k, 0 < a k)
    (C : ℕ → Chain (m + 1)) (hC : ∀ w k, (C w).block k ⊆ Finset.range N) :
    ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)),
      ∀ x : α → Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ,
      (∀ u, predictionLocalPrimeGoodEvent (maskGeneratedMaster m gap)
        ((maskGeneratedRowDataFamily m gap t).rows.catalog (maskGeneratedRowDataFamily m gap t).target)
        ((maskGeneratedRowDataFamily m gap t).rows.denominator (maskGeneratedRowDataFamily m gap t).target) w (x u)) →
      Nonempty (∀ u, (maskGeneratedRowDataFamily m gap t).rows.AdditiveEliminationConditions
        (maskGeneratedMaster m gap) w (masterColumnCoefficient N a (fun w => (C w).block) w) (x u)
        (maskGeneratedRowDataFamily m gap t).target) := by
  filter_upwards [maskGenerated_additive_elimination_data m gap a ha C hC] with w hw
  intro t x hg
  exact ⟨fun u => Classical.choice (hw t (x u) (hg u))⟩

theorem PolynomialRowFamily.AdditiveEliminationConditions.interval_power_bound {n r m : ℕ}
    {F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m}
    {master : MasterParameterFamily} {w : ℕ} {c : Fin (m + 1) → ℕ} {target : Fin r}
    {α : Type*} (x : α → Fin n → ℕ)
    (H : ∀ u, F.AdditiveEliminationConditions master w c (x u) target)
    (ρ : Mass α) (hρ : ∀ u, 0 ≤ ρ u) (L : α → ℕ) (hL : ∀ u, 0 < L u)
    (z : α → Fin (m + 1) → ℤ)
    (f Ω : α → ReplicaCubeRow (Fintype.card (PolynomialRowFamily.OffTargetRow target)) 1 → ℤ → ℝ)
    (hbound : ∀ u i y, |f u (some (additiveRowAssigned _ i)) y| ≤ Ω u (some (additiveRowAssigned _ i)) y) :
    |AdditiveRowData.orderedAverage ρ (fun u _ => uniformIntervalMass 0 (L u))
      (fun u => (H u).data) z f Ω 0| ^ (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow target)) ≤
      (AdditiveRowData.orderedPrefactorCap ρ (fun u _ => uniformIntervalMass 0 (L u))
        (fun u => (H u).data) z Ω) ^ (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow target) - 1) *
      |AdditiveRowData.orderedAverage ρ (fun u _ => uniformIntervalMass 0 (L u))
        (fun u => (H u).data) z f Ω (Fintype.card (PolynomialRowFamily.OffTargetRow target))| := by
  exact AdditiveRowData.ordered_average_power_bound ρ hρ _
    (fun u _ y => uniformIntervalMass_nonneg 0 (L u) y)
    (fun u _ => uniformIntervalMass_total 0 (hL u)) _ z f Ω hbound

theorem PolynomialRowFamily.AdditiveEliminationConditions.initial_product {n r m : ℕ}
    {F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m}
    {master : MasterParameterFamily} {w : ℕ} {c : Fin (m + 1) → ℕ} {x : Fin n → ℕ} {target : Fin r}
    (H : F.AdditiveEliminationConditions master w c x target) (z : Fin (m + 1) → ℤ)
    (v : Fin (Fintype.card (PolynomialRowFamily.OffTargetRow target)) → ℤ × ℤ)
    (f Ω : Fin r → ℤ → ℝ) :
    H.data.eliminationIntegrand ∅ z v (fun i => f (PolynomialRowFamily.additiveIndexEquiv target i))
      (fun i => Ω (PolynomialRowFamily.additiveIndexEquiv target i)) =
      ∏ j : Fin r, f j (F.normalizedIntegerLinearForm x c j
        (fun a => z a + ∑ k, (v k).1 * H.data.direction k a)) := by
  rw [H.data.eliminationIntegrand_empty]
  exact Fintype.prod_equiv (PolynomialRowFamily.additiveIndexEquiv target) _ _
    (fun i => by rw [H.form_eq])

theorem PolynomialRowFamily.AdditiveEliminationConditions.terminal_cube {n r m : ℕ}
    {F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m}
    {master : MasterParameterFamily} {w : ℕ} {c : Fin (m + 1) → ℕ} {x : Fin n → ℕ} {target : Fin r}
    (H : F.AdditiveEliminationConditions master w c x target) (z : Fin (m + 1) → ℤ)
    (v : Fin (Fintype.card (PolynomialRowFamily.OffTargetRow target)) → ℤ × ℤ)
    (f Ω : ReplicaCubeRow (Fintype.card (PolynomialRowFamily.OffTargetRow target)) 1 → ℤ → ℝ) :
    H.data.eliminationIntegrand Finset.univ z v f Ω =
      (∏ η : Fin (Fintype.card (PolynomialRowFamily.OffTargetRow target)) → Bool,
        f none (F.normalizedIntegerLinearForm x c target z +
          (F.translationModulus master w x target : ℤ) * ∑ k, predictionPairValues v k (η k))) *
      ∏ i : {r : ReplicaCubeRow (Fintype.card (PolynomialRowFamily.OffTargetRow target)) 1 // r ≠ none},
        H.data.stageFactorProduct Finset.univ i.val z (predictionPairValues v) (Ω i.val) := by
  rw [H.data.eliminationIntegrand_terminal_cube _ H.target_response, H.form_eq,
    PolynomialRowFamily.additiveIndexEquiv_root]

end Hindman168
