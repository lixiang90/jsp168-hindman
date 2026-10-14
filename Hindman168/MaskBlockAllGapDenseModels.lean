import Hindman168.MaskBlockGapTemplates

/-! One dense model at a block controls every permissible constant gap,
every actual mask row, the zero-prime nilsequence test and every fixed
positive quotient scale. The model is selected before a later gap or chain.
All tests use the unchanged original master and harmonic root mass. -/

namespace Hindman168
open Filter
open scoped Topology Classical
open FiniteMass

theorem maskBlock_all_gap_dense_models (m d₀ : ℕ) (hd₀ : 0 < d₀)
    {N : ℕ} (hN : 0 < N) (A : Finset ℚ) (hA : ∀ a ∈ A, 0 < a)
    (T : Finset ℕ) (i : Fin N) (hT : T.Nonempty) (hTi : T ⊆ Finset.range i.val)
    (ρ : ℕ → ℤ → ℝ)
    (hρ : ∀ᶠ w in atTop, ∀ y, 0 ≤ ρ w y ∧ ρ w y ≤
      masterPredictionBlockMask (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
        (fun _ => maskBlockChain T i.val hT hTi) (fun _ => 0) w y)
    (P : ℕ → ℕ → Prop) (hP : ∀ q, ∀ᶠ w in atTop, P q w) :
    ∃ (stage : ℕ → ℕ) (model : ℕ → ℤ → ℝ), Tendsto stage atTop atTop ∧
      (∀ w, stage w ≤ w) ∧ (∀ w y, 0 ≤ model w y ∧ model w y ≤ 1) ∧
      (∀ᶠ w in atTop, P (stage w) w) ∧
      ∀ l : MaskValidBlockGap T i,
        ∀ t : Fin (Fintype.card (LargeColumnSubset m) + 1),
        ∀ J : ℕ, 1 ≤ J → ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
        ∀ u : OriginalSingleDualInput
          (maskGeneratedDualTemplates m (fun _ => l.val) d₀ (fun _ => l.val) t).arity
          (maskGeneratedDualTemplates m (fun _ => l.val) d₀ (fun _ => l.val) t).dimension,
        u.Admissible (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
          (fun _ => maskBlockChain T i.val hT hTi) (fun _ => 0) w →
        |expectation (integerMass ((maskGeneratedMaster m (fun _ => ⟨0, hN⟩)).cutoff w i.val)
          (primorial w)) (fun y => (ρ w y - model w y) *
            (maskGeneratedDualTemplates m (fun _ => l.val) d₀ (fun _ => l.val) t).dual
              (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) (fun _ => J) u w y)| < η := by
  let B := MaskValidBlockGap T i × Fin (Fintype.card (LargeColumnSubset m) + 1)
  let e := Fintype.equivFin B
  let templates (z : Fin (Fintype.card B)) :=
    maskGeneratedDualTemplates m (fun _ => (e.symm z).1.val) d₀
      (fun _ => (e.symm z).1.val) (e.symm z).2
  have htemplates (z : Fin (Fintype.card B)) :
      OriginalDualTemplateConditions (templates z)
        (originalRowMasterCatalog (maskGeneratedRowDataFamily m (fun _ => ⟨0, hN⟩)))
        (max d₀ (maskRowCountBound m)) (fun _ => T) (fun _ => i) :=
    maskBlockGap_templates_conditions m d₀ hd₀ hN T i (e.symm z).1 (e.symm z).2
  obtain ⟨stage, model, hs, hsmall, hb, hp, he⟩ :=
    (maskGeneratedMaster_conditions m (fun _ => ⟨0, hN⟩) A hA).finite_templates_all_positive_scales_dense_models
        (originalRowMasterCatalog_nonzero (maskGeneratedRowDataFamily m (fun _ => ⟨0, hN⟩)))
        templates (fun _ => maskBlockChain T i.val hT hTi)
        (fun _ => maskBlockChain_block_range T i hT hTi) (fun _ => 0)
        (fun _ => T) (Eventually.of_forall (fun _ => Finset.Subset.refl _))
        (fun _ => i) (Eventually.of_forall (fun _ => hTi)) htemplates ρ hρ P hP
  refine ⟨stage, model, hs, hsmall, hb, hp, ?_⟩
  intro l t J hJ η hη
  have hen : e.symm (e (l, t)) = (l, t) := e.symm_apply_apply (l, t)
  have heq : templates (e (l, t)) =
      maskGeneratedDualTemplates m (fun _ => l.val) d₀ (fun _ => l.val) t := by
    change maskGeneratedDualTemplates m (fun _ => (e.symm (e (l, t))).1.val) d₀
      (fun _ => (e.symm (e (l, t))).1.val) (e.symm (e (l, t))).2 = _
    rw [hen]
  have hx := he (e (l, t)) J hJ η hη
  rw [heq] at hx
  exact hx

end Hindman168
