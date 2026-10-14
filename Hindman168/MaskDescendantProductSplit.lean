import Hindman168.MaskFreshPrimeTupleLaw

/-! Exact finite multiplicities in a mask row update: one descendant of
an invariant row and two Bool-indexed descendants of a noninvariant row. -/

namespace Hindman168

open scoped BigOperators Classical

variable {R : Type*} [CommRing R] {r m : ℕ}

abbrev MaskInvariantRowIndex (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3) :=
  {i : Fin r // maskRowInvariant (F.row i) tag}

abbrev MaskNoninvariantRowIndex (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3) :=
  {i : Fin r // ¬ maskRowInvariant (F.row i) tag}

noncomputable instance (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3) :
    Fintype (MaskInvariantRowIndex F tag) := Fintype.ofFinite _

noncomputable instance (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3) :
    Fintype (MaskNoninvariantRowIndex F tag) := Fintype.ofFinite _

def maskInvariantCopy (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3)
    (i : Fin r) (hi : maskRowInvariant (F.row i) tag) : MaskDescendant F tag :=
  ⟨(i, none), Or.inl ⟨hi, rfl⟩⟩

noncomputable def maskDescendantSplit (F : PolynomialRowFamily R r m)
    (tag : Fin (m + 1) → Fin 3) (d : MaskDescendant F tag) :
    MaskInvariantRowIndex F tag ⊕ (MaskNoninvariantRowIndex F tag × Bool) :=
  if hi : maskRowInvariant (F.row d.val.1) tag then Sum.inl ⟨d.val.1, hi⟩
  else Sum.inr (⟨d.val.1, hi⟩, d.val.2.getD false)

noncomputable def maskDescendantUnsplit (F : PolynomialRowFamily R r m)
    (tag : Fin (m + 1) → Fin 3) :
    MaskInvariantRowIndex F tag ⊕ (MaskNoninvariantRowIndex F tag × Bool) → MaskDescendant F tag :=
  Sum.elim (fun i => maskInvariantCopy F tag i.val i.property)
    (fun ib => maskNoninvariantCopy F tag ib.1.val ib.1.property ib.2)

theorem maskDescendantUnsplit_split (F : PolynomialRowFamily R r m)
    (tag : Fin (m + 1) → Fin 3) (d : MaskDescendant F tag) :
    maskDescendantUnsplit F tag (maskDescendantSplit F tag d) = d := by
  unfold maskDescendantSplit
  split_ifs with hi
  · apply Subtype.ext
    change (d.val.1, none) = d.val
    apply Prod.ext
    · rfl
    · exact ((maskDescendant_none_iff F tag d).mpr hi).symm
  · obtain ⟨b, hb⟩ := maskDescendant_some_of_noninvariant F tag d hi
    apply Subtype.ext
    change (d.val.1, some (d.val.2.getD false)) = d.val
    apply Prod.ext
    · rfl
    · simp [hb]

theorem maskDescendantSplit_unsplit (F : PolynomialRowFamily R r m)
    (tag : Fin (m + 1) → Fin 3)
    (a : MaskInvariantRowIndex F tag ⊕ (MaskNoninvariantRowIndex F tag × Bool)) :
    maskDescendantSplit F tag (maskDescendantUnsplit F tag a) = a := by
  cases a with
  | inl i => simp [maskDescendantSplit, maskDescendantUnsplit, maskInvariantCopy, i.property]
  | inr ib =>
    rcases ib with ⟨i, b⟩
    simp [maskDescendantSplit, maskDescendantUnsplit, maskNoninvariantCopy, i.property]

noncomputable def maskDescendantSplitEquiv (F : PolynomialRowFamily R r m)
    (tag : Fin (m + 1) → Fin 3) :
    MaskDescendant F tag ≃ MaskInvariantRowIndex F tag ⊕ (MaskNoninvariantRowIndex F tag × Bool) where
  toFun := maskDescendantSplit F tag
  invFun := maskDescendantUnsplit F tag
  left_inv := maskDescendantUnsplit_split F tag
  right_inv := maskDescendantSplit_unsplit F tag

theorem maskDescendant_product_split {A : Type*} [CommMonoid A]
    (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3) (f : MaskDescendant F tag → A) :
    (∏ d, f d) =
      (∏ i : MaskInvariantRowIndex F tag, f (maskInvariantCopy F tag i.val i.property)) *
      (∏ i : MaskNoninvariantRowIndex F tag,
        f (maskNoninvariantCopy F tag i.val i.property false) *
        f (maskNoninvariantCopy F tag i.val i.property true)) := by
  have he := Fintype.prod_equiv (maskDescendantSplitEquiv F tag) f
    (fun a => f (maskDescendantUnsplit F tag a))
    (by
      intro d
      change f d = f (maskDescendantUnsplit F tag (maskDescendantSplit F tag d))
      rw [maskDescendantUnsplit_split])
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type] at he
  calc
    _ = (∏ i : MaskInvariantRowIndex F tag, f (maskInvariantCopy F tag i.val i.property)) *
        (∏ i : MaskNoninvariantRowIndex F tag, ∏ b : Bool,
          f (maskNoninvariantCopy F tag i.val i.property b)) := he
    _ = _ := by
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [Fintype.prod_bool]
      exact mul_comm _ _

end Hindman168
