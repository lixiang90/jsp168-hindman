import Hindman168.MaskRowFamilyStep

/-! The actual initial row family consists of all nonempty subset indicators. -/

namespace Hindman168

open scoped BigOperators Classical

abbrev NonemptyColumnSubset (c : ℕ) := {S : Finset (Fin c) // S.Nonempty}

noncomputable instance (c : ℕ) : Fintype (NonemptyColumnSubset c) := Fintype.ofFinite _

noncomputable def columnSubsetIndicator {R : Type*} [Zero R] [One R] {c : ℕ}
    (S : Finset (Fin c)) : Fin c → R := fun k => if k ∈ S then 1 else 0

theorem columnSubsetIndicator_nonzero_iff {R : Type*} [CommRing R] [Nontrivial R] {c : ℕ}
    (S : Finset (Fin c)) (k : Fin c) : columnSubsetIndicator (R := R) S k ≠ 0 ↔ k ∈ S := by
  simp [columnSubsetIndicator]

theorem distinct_columnSubsetIndicator_minor {R : Type*}
    [CommRing R] [Nontrivial R] {c : ℕ}
    (S T : Finset (Fin c)) (hS : S.Nonempty) (hT : T.Nonempty) (hne : S ≠ T) :
    ∃ j k, polynomialRowMinor (columnSubsetIndicator (R := R) S) (columnSubsetIndicator T) j k ≠ 0 := by
  have hex : ∃ j, ¬ (j ∈ S ↔ j ∈ T) := by
    by_contra! h
    exact hne (Finset.ext h)
  obtain ⟨j, hj⟩ := hex
  by_cases hjS : j ∈ S
  · have hjT : j ∉ T := by intro ht; exact hj (iff_of_true hjS ht)
    obtain ⟨k, hk⟩ := hT
    exact ⟨j, k, by simp [polynomialRowMinor, columnSubsetIndicator, hjS, hjT, hk]⟩
  · have hjT : j ∈ T := by
      by_contra ht
      exact hj (iff_of_false hjS ht)
    obtain ⟨k, hk⟩ := hS
    exact ⟨j, k, by simp [polynomialRowMinor, columnSubsetIndicator, hjS, hjT, hk]⟩

theorem nonemptyColumnSubset_card (c : ℕ) :
    Fintype.card (NonemptyColumnSubset c) = 2 ^ c - 1 := by
  have hcard := Fintype.card_of_subtype (p := fun S : Finset (Fin c) => S.Nonempty)
    ((Finset.univ : Finset (Fin c)).powerset.erase ∅)
    (fun S : Finset (Fin c) => by simp [Finset.nonempty_iff_ne_empty])
  have he : (∅ : Finset (Fin c)) ∈ (Finset.univ : Finset (Fin c)).powerset := by simp
  change Fintype.card {S : Finset (Fin c) // S.Nonempty} = _
  rw [hcard, Finset.card_erase_of_mem he, Finset.card_powerset, Finset.card_univ, Fintype.card_fin]

noncomputable def initialMaskRowFamily {R : Type*} [CommRing R] [Nontrivial R] (m : ℕ) :
    PolynomialRowFamily R (Fintype.card (NonemptyColumnSubset (m + 1))) m where
  row i := columnSubsetIndicator ((Fintype.equivFin (NonemptyColumnSubset (m + 1))).symm i).val
  anchor i := Classical.choose ((Fintype.equivFin (NonemptyColumnSubset (m + 1))).symm i).property
  anchor_ne_zero i := (columnSubsetIndicator_nonzero_iff _ _).mpr
    (Classical.choose_spec ((Fintype.equivFin (NonemptyColumnSubset (m + 1))).symm i).property)
  pair_minor i l hl := distinct_columnSubsetIndicator_minor _ _
    ((Fintype.equivFin (NonemptyColumnSubset (m + 1))).symm i).property
    ((Fintype.equivFin (NonemptyColumnSubset (m + 1))).symm l).property
    (fun he => hl ((Fintype.equivFin (NonemptyColumnSubset (m + 1))).symm.injective
      (Subtype.ext he)).symm)

noncomputable def initialMaskRowIndex {m : ℕ} (S : Finset (Fin (m + 1))) (hS : S.Nonempty) :
    Fin (Fintype.card (NonemptyColumnSubset (m + 1))) := Fintype.equivFin _ ⟨S, hS⟩

theorem initialMaskRowFamily_row {R : Type*} [CommRing R] [Nontrivial R] {m : ℕ}
    (S : Finset (Fin (m + 1))) (hS : S.Nonempty) :
    (initialMaskRowFamily (R := R) m).row (initialMaskRowIndex S hS) = columnSubsetIndicator S := by
  simp [initialMaskRowFamily, initialMaskRowIndex]

theorem nonemptyColumnSubset_card_ge {c : ℕ} (S : Finset (Fin c)) :
    S.card ≤ Fintype.card (NonemptyColumnSubset c) := by
  let f (k : S) : NonemptyColumnSubset c := ⟨{k.val}, Finset.singleton_nonempty _⟩
  have hi : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    exact Finset.singleton_injective (congrArg Subtype.val he)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi

end Hindman168
