import Hindman168.MasterTemplateUnionDenseModels
import Hindman168.OriginalTemplateScaleIndices
import Hindman168.CountableDenseModelDiagonal
import Mathlib.Data.Countable.Defs

/-!
# A common asymptotic bounded model for countably many original templates

Each fixed template retains its own constant positive quotient scale. A
finite prefix is reindexed exactly into one finite scale array; the actual
finite-union model theorem supplies its model estimate. The slow diagonal
then yields one model sequence for every fixed original template and scale.
The original master list/family stay fixed independently of the prefix.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def originalCountableTestClass {n N m : ℕ}
    (T : ℕ → OriginalDualTemplate n N 1) (F : MasterParameterFamily)
    (C : ℕ → Chain m) (label : ℕ → Fin m) (J : ℕ → ℕ) (t w : ℕ) : Set (ℤ → ℝ) :=
  {g | ∃ u : OriginalSingleDualInput (T t).arity (T t).dimension,
    u.Admissible F C label w ∧ g = fun y => (T t).dual F (fun _ => J t) u w y}

theorem MasterParameterConditions.countable_original_dense_models
    {n N m d : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0)
    (T : ℕ → OriginalDualTemplate n N 1)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N) (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (hT : ∀ t, OriginalDualTemplateConditions (T t) D d tail root)
    (J : ℕ → ℕ) (hJ : ∀ t, 1 ≤ J t)
    (ρ : ℕ → ℤ → ℝ)
    (hρ : ∀ᶠ w in atTop, ∀ y, 0 ≤ ρ w y ∧ ρ w y ≤ masterPredictionBlockMask F C label w y)
    (P : ℕ → ℕ → Prop) (hP : ∀ q, ∀ᶠ w in atTop, P q w) :
    ∃ (stage : ℕ → ℕ) (model : ℕ → ℤ → ℝ), Tendsto stage atTop atTop ∧
      (∀ w, stage w ≤ w) ∧ (∀ w y, 0 ≤ model w y ∧ model w y ≤ 1) ∧
      (∀ᶠ w in atTop, P (stage w) w) ∧
      ∀ t : ℕ, ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
        ∀ u : OriginalSingleDualInput (T t).arity (T t).dimension,
          u.Admissible F C label w →
          |expectation (integerMass (F.cutoff w (root w).val) (primorial w))
            (fun y => (ρ w y - model w y) * (T t).dual F (fun _ => J t) u w y)| < η := by
  let μ w := integerMass (F.cutoff w (root w).val) (primorial w)
  let S := originalCountableTestClass T F C label J
  have hmodels (q : ℕ) : ∀ᶠ w in atTop, ∃ model : ℤ → ℝ,
      (∀ y, 0 ≤ model y ∧ model y ≤ 1) ∧
      ∀ t : ℕ, t ≤ q → ∀ g ∈ S t w,
        |expectation (μ w) (fun y => (ρ w y - model y) * g y)| ≤ 1 / ((q : ℝ) + 1) := by
    let Tq (t : Fin (q + 1)) := (T t.val).withScaleIndex t
    let Jq (t : Fin (q + 1)) := J t.val
    have hTq (t : Fin (q + 1)) : OriginalDualTemplateConditions (Tq t) D d tail root :=
      (T t.val).withScaleIndex_conditions t D tail root (hT t.val)
    have hJq (t : Fin (q + 1)) : 1 ≤ Jq t := hJ t.val
    let cut := predictionDualThreshold d + 1
    have hcut : predictionDualThreshold d < cut := by dsimp only [cut]; linarith
    have hm := hF.uniform_template_union_original_dense_models hD Tq C hN label tail htail root
      htailroot hTq Jq hJq cut hcut (1 / ((q : ℝ) + 1)) (by positivity)
    filter_upwards [hm, hρ] with w hmw hρw
    obtain ⟨model, hb, he⟩ := hmw (ρ w) hρw
    refine ⟨model, hb, ?_⟩
    intro t ht g hg
    obtain ⟨u, hu, rfl⟩ := hg
    let index : Fin (q + 1) := ⟨t, by omega⟩
    have hx := he index u hu
    change |expectation (μ w) (fun y => (ρ w y - model y) *
      ((T t).withScaleIndex index).dual F Jq u w y)| < 1 / ((q : ℝ) + 1) at hx
    simp only [OriginalDualTemplate.dual_withScaleIndex] at hx
    exact hx.le
  obtain ⟨stage, model, hs, hsmall, hb, hp, he⟩ := countable_dense_model_diagonal μ ρ S P hP hmodels
  refine ⟨stage, model, hs, hsmall, hb, hp, ?_⟩
  intro t η hη
  filter_upwards [he t η hη] with w hw
  intro u hu
  exact hw (fun y => (T t).dual F (fun _ => J t) u w y) ⟨u, hu, rfl⟩


theorem MasterParameterConditions.finite_templates_all_positive_scales_dense_models
    {n N m d L : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0)
    (T : Fin L → OriginalDualTemplate n N 1)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N) (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (hT : ∀ t, OriginalDualTemplateConditions (T t) D d tail root)
    (ρ : ℕ → ℤ → ℝ)
    (hρ : ∀ᶠ w in atTop, ∀ y, 0 ≤ ρ w y ∧ ρ w y ≤ masterPredictionBlockMask F C label w y)
    (P : ℕ → ℕ → Prop) (hP : ∀ q, ∀ᶠ w in atTop, P q w) :
    ∃ (stage : ℕ → ℕ) (model : ℕ → ℤ → ℝ), Tendsto stage atTop atTop ∧
      (∀ w, stage w ≤ w) ∧ (∀ w y, 0 ≤ model w y ∧ model w y ≤ 1) ∧
      (∀ᶠ w in atTop, P (stage w) w) ∧
      ∀ t : Fin L, ∀ j : ℕ, 1 ≤ j → ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
        ∀ u : OriginalSingleDualInput (T t).arity (T t).dimension,
          u.Admissible F C label w →
          |expectation (integerMass (F.cutoff w (root w).val) (primorial w))
            (fun y => (ρ w y - model w y) * (T t).dual F (fun _ => j) u w y)| < η := by
  rcases Nat.eq_zero_or_pos L with hz | hL
  · subst L
    obtain ⟨stage, hs, hsmall, hp⟩ := exists_slow_stage P hP
    refine ⟨stage, fun _ _ => 0, hs, hsmall, fun _ _ => by norm_num, hp, ?_⟩
    intro t
    exact Fin.elim0 t
  · letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
    obtain ⟨enumeration, henum⟩ := exists_surjective_nat (Fin L × ℕ)
    let Tseq k := T (enumeration k).1
    let Jseq k := (enumeration k).2 + 1
    obtain ⟨stage, model, hs, hsmall, hb, hp, he⟩ := hF.countable_original_dense_models hD
      Tseq C hN label tail htail root htailroot (fun k => hT (enumeration k).1)
      Jseq (fun k => by dsimp only [Jseq]; omega) ρ hρ P hP
    refine ⟨stage, model, hs, hsmall, hb, hp, ?_⟩
    intro t j hj η hη
    obtain ⟨k, hk⟩ := henum (t, j - 1)
    have ht : (enumeration k).1 = t := congrArg Prod.fst hk
    have hjIndex : (enumeration k).2 + 1 = j := by
      rw [show (enumeration k).2 = j - 1 from congrArg Prod.snd hk, Nat.sub_add_cancel hj]
    have hx := he k η hη
    dsimp only [Tseq, Jseq] at hx
    rw [ht, hjIndex] at hx
    exact hx

end Hindman168
