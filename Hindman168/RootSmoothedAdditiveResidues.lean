import Hindman168.RootSmoothedAdditiveRows

/-! Root smoothing preserves primitive rows and pair independence.
Different old copies are separated on old columns. Two copies of the same
old row are separated on a nonzero root-response column. -/

namespace Hindman168.AdditiveRowData

open scoped BigOperators Classical

variable {b c : ℕ}

structure RootResidueConditions (D : AdditiveRowData b c) (v₀ : Fin c → ℤ) (p : ℕ) : Prop where
  old : D.ResidueConditions p
  root_unit : ∀ i, i ≠ none → IsUnit (D.form i v₀ : ZMod p)

theorem RootResidueConditions.primitive {D : AdditiveRowData b c} {v₀ : Fin c → ℤ} {p : ℕ}
    (H : D.RootResidueConditions v₀ p) (r : RootSmoothedAdditiveCopy b) :
    ∃ j, (D.rootSmoothedCoefficient v₀ r j : ZMod p) ≠ 0 := by
  obtain ⟨j, hj⟩ := H.old.copied_primitive r.val.1
  exact ⟨.inl j, hj⟩

theorem RootResidueConditions.pair_independent
    {D : AdditiveRowData b c} {v₀ : Fin c → ℤ} {p : ℕ}
    (H : D.RootResidueConditions v₀ p) (hp : p.Prime)
    (r s : RootSmoothedAdditiveCopy b) (hrs : r ≠ s) :
    LinearIndependent (ZMod p)
      ![(fun j => (D.rootSmoothedCoefficient v₀ r j : ZMod p)),
        (fun j => (D.rootSmoothedCoefficient v₀ s j : ZMod p))] := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hold : r.val.1 = s.val.1
  · have hbit : r.val.2 ≠ s.val.2 := by
      intro he
      exact hrs (Subtype.ext (Prod.ext hold he))
    have hbase : r.val.1.val.1 ≠ none := by
      intro he
      have hs : s.val.1.val.1 = none := (congrArg (fun q => q.val.1) hold).symm.trans he
      exact hbit ((r.property he).trans (s.property hs).symm)
    apply rows_pair_independent_of_zero_coordinate _ _ (.inr r.val.2)
    · simpa only [rootSmoothedCoefficient, ite_true] using (H.root_unit _ hbase).ne_zero
    · simp only [rootSmoothedCoefficient, if_neg hbit, Int.cast_zero]
    · exact H.primitive s
  · apply LinearIndependent.pair_iff.mpr
    intro a e h
    apply (LinearIndependent.pair_iff.mp (H.old.copied_pair_independent hp _ _ hold)) a e
    funext j
    exact congrFun h (.inl j)

theorem RootResidueConditions.fin_primitive
    {D : AdditiveRowData b c} {v₀ : Fin c → ℤ} {p : ℕ}
    (H : D.RootResidueConditions v₀ p) (r : RootSmoothedAdditiveCopy b) :
    ∃ j, (D.rootSmoothedFinCoefficient v₀ r j : ZMod p) ≠ 0 := by
  obtain ⟨j, hj⟩ := H.primitive r
  refine ⟨Fintype.equivFin (RootSmoothedAdditiveColumn b c) j, ?_⟩
  simpa only [rootSmoothedFinCoefficient, Equiv.symm_apply_apply] using hj

theorem RootResidueConditions.fin_pair_independent
    {D : AdditiveRowData b c} {v₀ : Fin c → ℤ} {p : ℕ}
    (H : D.RootResidueConditions v₀ p) (hp : p.Prime)
    (r s : RootSmoothedAdditiveCopy b) (hrs : r ≠ s) :
    LinearIndependent (ZMod p)
      ![(fun j => (D.rootSmoothedFinCoefficient v₀ r j : ZMod p)),
        (fun j => (D.rootSmoothedFinCoefficient v₀ s j : ZMod p))] := by
  apply LinearIndependent.pair_iff.mpr
  intro a e h
  apply (LinearIndependent.pair_iff.mp (H.pair_independent hp r s hrs)) a e
  funext j
  have hj := congrFun h (Fintype.equivFin (RootSmoothedAdditiveColumn b c) j)
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    rootSmoothedFinCoefficient, Equiv.symm_apply_apply] using hj

end Hindman168.AdditiveRowData
