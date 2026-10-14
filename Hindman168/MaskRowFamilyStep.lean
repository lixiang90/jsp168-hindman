import Hindman168.MaskRowInvariance

/-!
# Actual finite row-family update for one mask removal

An invariant row contributes exactly one retained row; a noninvariant row
contributes exactly the two new prime branches. Every surviving row keeps
its support and an explicit old anchor. All pair-minor evidence is derived,
and the number of rows is at most twice the old number.
-/

namespace Hindman168

open scoped BigOperators Classical

abbrev MaskDescendant {R : Type*} [CommRing R] {r m : ℕ}
    (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3) :=
  {p : Fin r × Option Bool //
    (maskRowInvariant (F.row p.1) tag ∧ p.2 = none) ∨
    (¬ maskRowInvariant (F.row p.1) tag ∧ p.2 ≠ none)}

noncomputable instance {R : Type*} [CommRing R] {r m : ℕ}
    (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3) :
    Fintype (MaskDescendant F tag) := Fintype.ofFinite _

noncomputable def maskDescendantRow {R : Type*} [CommRing R] {r m : ℕ}
    (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3)
    (x : MaskDescendant F tag) : Fin (m + 1) → MvPolynomial Bool R :=
  maskBranchRow (F.row x.val.1) tag x.val.2

theorem maskDescendant_none_iff {R : Type*} [CommRing R] {r m : ℕ}
    (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3)
    (x : MaskDescendant F tag) :
    x.val.2 = none ↔ maskRowInvariant (F.row x.val.1) tag := by
  rcases x.property with h | h
  · exact ⟨fun _ => h.1, fun _ => h.2⟩
  · exact ⟨fun hn => (h.2 hn).elim, fun hi => (h.1 hi).elim⟩

theorem maskDescendant_some_of_noninvariant {R : Type*} [CommRing R] {r m : ℕ}
    (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3)
    (x : MaskDescendant F tag) (hi : ¬ maskRowInvariant (F.row x.val.1) tag) :
    ∃ b, x.val.2 = some b := by
  cases hx : x.val.2 with
  | none => exact (hi ((maskDescendant_none_iff F tag x).mp hx)).elim
  | some b => exact ⟨b, rfl⟩

def maskNoninvariantCopy {R : Type*} [CommRing R] {r m : ℕ}
    (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3)
    (i : Fin r) (hi : ¬ maskRowInvariant (F.row i) tag) (b : Bool) : MaskDescendant F tag :=
  ⟨(i, some b), Or.inr ⟨hi, Option.some_ne_none b⟩⟩

theorem maskDescendant_anchor_nonzero {R : Type*} [CommRing R] {r m : ℕ}
    (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3)
    (x : MaskDescendant F tag) : maskDescendantRow F tag x (F.anchor x.val.1) ≠ 0 :=
  (maskBranchRow_ne_zero_iff _ _ _ _).mpr (F.anchor_ne_zero x.val.1)

theorem maskDescendant_support_iff {R : Type*} [CommRing R] {r m : ℕ}
    (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3)
    (x : MaskDescendant F tag) (k : Fin (m + 1)) :
    maskDescendantRow F tag x k ≠ 0 ↔ F.row x.val.1 k ≠ 0 :=
  maskBranchRow_ne_zero_iff _ _ _ _

theorem maskDescendant_pair_minor {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R] {r m : ℕ}
    (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3)
    (x y : MaskDescendant F tag) (hne : x ≠ y) :
    ∃ j k, polynomialRowMinor (maskDescendantRow F tag x) (maskDescendantRow F tag y) j k ≠ 0 := by
  by_cases ho : x.val.1 = y.val.1
  · have hb : x.val.2 ≠ y.val.2 := by
      intro hb
      exact hne (Subtype.ext (Prod.ext ho hb))
    have hi : ¬ maskRowInvariant (F.row x.val.1) tag := by
      intro hi
      have hy : maskRowInvariant (F.row y.val.1) tag := by simpa only [ho] using hi
      exact hb ((maskDescendant_none_iff F tag x).mpr hi |>.trans
        ((maskDescendant_none_iff F tag y).mpr hy).symm)
    have hiy : ¬ maskRowInvariant (F.row y.val.1) tag := by simpa only [ho] using hi
    obtain ⟨a, ha⟩ := maskDescendant_some_of_noninvariant F tag x hi
    obtain ⟨b, hb'⟩ := maskDescendant_some_of_noninvariant F tag y hiy
    have hab : a ≠ b := by
      intro hab
      exact hb (ha.trans ((congrArg some hab).trans hb'.symm))
    change ∃ j k, polynomialRowMinor (maskBranchRow (F.row x.val.1) tag x.val.2)
      (maskBranchRow (F.row y.val.1) tag y.val.2) j k ≠ 0
    rw [← ho, ha, hb']
    exact noninvariant_maskBranchRow_pair_minor _ _ hi a b hab
  · obtain ⟨j, k, hjk⟩ := F.pair_minor x.val.1 y.val.1 (Ne.symm ho)
    exact ⟨j, k, maskBranchRow_old_minor_nonzero _ _ tag _ _ j k hjk⟩

theorem maskDescendant_encoding_injective {R : Type*} [CommRing R] {r m : ℕ}
    (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3) :
    Function.Injective (fun x : MaskDescendant F tag => (x.val.1, x.val.2.getD false)) := by
  intro x y h
  have ho : x.val.1 = y.val.1 := congrArg (fun p : Fin r × Bool => p.1) h
  have hd : x.val.2.getD false = y.val.2.getD false := congrArg (fun p : Fin r × Bool => p.2) h
  apply Subtype.ext
  apply Prod.ext ho
  cases hx : x.val.2 with
  | none =>
    have hi := (maskDescendant_none_iff F tag x).mp hx
    have hiy : maskRowInvariant (F.row y.val.1) tag := by simpa only [ho] using hi
    exact ((maskDescendant_none_iff F tag y).mpr hiy).symm
  | some a =>
    cases hy : y.val.2 with
    | none =>
      have hi := (maskDescendant_none_iff F tag y).mp hy
      have hix : maskRowInvariant (F.row x.val.1) tag := by simpa only [ho] using hi
      simpa only [hx] using ((maskDescendant_none_iff F tag x).mpr hix)
    | some b =>
      have hab : a = b := by simpa only [hx, hy, Option.getD_some] using hd
      exact congrArg some hab

theorem maskDescendant_card_le {R : Type*} [CommRing R] {r m : ℕ}
    (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3) :
    Fintype.card (MaskDescendant F tag) ≤ 2 * r := by
  have h := Fintype.card_le_of_injective _ (maskDescendant_encoding_injective F tag)
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm] using h

noncomputable def PolynomialRowFamily.maskStep {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R] {r m : ℕ}
    (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3) :
    PolynomialRowFamily (MvPolynomial Bool R) (Fintype.card (MaskDescendant F tag)) m where
  row i := maskDescendantRow F tag ((Fintype.equivFin _).symm i)
  anchor i := F.anchor ((Fintype.equivFin (MaskDescendant F tag)).symm i).val.1
  anchor_ne_zero i := maskDescendant_anchor_nonzero F tag ((Fintype.equivFin _).symm i)
  pair_minor i l hl := maskDescendant_pair_minor F tag ((Fintype.equivFin _).symm i) ((Fintype.equivFin _).symm l)
    (fun hi => hl ((Fintype.equivFin (MaskDescendant F tag)).symm.injective hi).symm)

noncomputable def maskPreferredDescendant {R : Type*} [CommRing R] {r m : ℕ}
    (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3) (i : Fin r) :
    MaskDescendant F tag :=
  if h : maskRowInvariant (F.row i) tag then ⟨(i, none), Or.inl ⟨h, rfl⟩⟩
  else maskNoninvariantCopy F tag i h false

theorem maskPreferredDescendant_origin {R : Type*} [CommRing R] {r m : ℕ}
    (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3) (i : Fin r) :
    (maskPreferredDescendant F tag i).val.1 = i := by
  unfold maskPreferredDescendant
  split_ifs <;> rfl

theorem maskDescendant_card_ge {R : Type*} [CommRing R] {r m : ℕ}
    (F : PolynomialRowFamily R r m) (tag : Fin (m + 1) → Fin 3) :
    r ≤ Fintype.card (MaskDescendant F tag) := by
  have hi : Function.Injective (maskPreferredDescendant F tag) := by
    intro i j h
    have he := congrArg (fun x : MaskDescendant F tag => x.val.1) h
    simpa only [maskPreferredDescendant_origin] using he
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hi

end Hindman168
