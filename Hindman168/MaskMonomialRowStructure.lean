import Hindman168.CoefficientOneMonomials
import Hindman168.InitialMaskIndicatorRows

/-!
# Monomial and one-variable-per-column certificates for actual mask rows

The variable certificate concerns each individual row; a variable may occur
in different columns of different rows. Old slots and the two new slots are
disjoint. This supplies the exact invariant required by the preprint.
-/

namespace Hindman168

open scoped BigOperators Classical

structure PolynomialMonomialRow {n c : ℕ} (A : Fin c → MvPolynomial (Fin n) ℤ) : Prop where
  entries : ∀ k, A k = 0 ∨ CoefficientOneMonomial (A k)
  variable_unique : ∀ v j k, v ∈ (A j).vars → v ∈ (A k).vars → j = k

def PolynomialRowFamily.MonomialStructure {n r m : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m) : Prop :=
  ∀ i, PolynomialMonomialRow (F.row i)

noncomputable def flattenedMaskBranchRow {n c : ℕ} (A : Fin c → MvPolynomial (Fin n) ℤ)
    (tag : Fin c → Fin 3) (b : Option Bool) : Fin c → MvPolynomial (Fin (2 + n)) ℤ :=
  fun k => MvPolynomial.rename (freshMaskOldSlot n) (A k) *
    b.elim 1 (fun bb => flattenedFreshMaskMultiplier n bb (tag k))

theorem PolynomialMonomialRow.flattened_branch {n c : ℕ}
    (A : Fin c → MvPolynomial (Fin n) ℤ) (hA : PolynomialMonomialRow A)
    (tag : Fin c → Fin 3)
    (htag : ∀ j k, tag j = tag k → tag j ≠ 0 → j = k) (b : Option Bool) :
    PolynomialMonomialRow (flattenedMaskBranchRow A tag b) := by
  constructor
  · intro k
    rcases hA.entries k with hz | hm
    · exact Or.inl (by simp [flattenedMaskBranchRow, hz])
    · apply Or.inr
      apply CoefficientOneMonomial.mul (hm.rename (freshMaskOldSlot n))
      cases b with
      | none => exact coefficientOneMonomial_one _
      | some b => exact flattenedFreshMaskMultiplier_monomial n b (tag k)
  · intro v j k hj hk
    cases b with
    | none =>
      simp only [flattenedMaskBranchRow, Option.elim_none, mul_one] at hj hk
      obtain ⟨a, ha, hav⟩ := MvPolynomial.mem_vars_rename (freshMaskOldSlot n) (A j) hj
      obtain ⟨d, hd, hdv⟩ := MvPolynomial.mem_vars_rename (freshMaskOldSlot n) (A k) hk
      have had : a = d := freshMaskOldSlot_injective n (hav.trans hdv.symm)
      subst d
      exact hA.variable_unique a j k ha hd
    | some b =>
      change v ∈ (MvPolynomial.rename (freshMaskOldSlot n) (A j) *
        flattenedFreshMaskMultiplier n b (tag j)).vars at hj
      change v ∈ (MvPolynomial.rename (freshMaskOldSlot n) (A k) *
        flattenedFreshMaskMultiplier n b (tag k)).vars at hk
      have hj' := MvPolynomial.vars_mul _ _ hj
      have hk' := MvPolynomial.vars_mul _ _ hk
      rcases Finset.mem_union.mp hj' with hjo | hjf
      · rcases Finset.mem_union.mp hk' with hko | hkf
        · obtain ⟨a, ha, hav⟩ := MvPolynomial.mem_vars_rename (freshMaskOldSlot n) (A j) hjo
          obtain ⟨d, hd, hdv⟩ := MvPolynomial.mem_vars_rename (freshMaskOldSlot n) (A k) hko
          have had : a = d := freshMaskOldSlot_injective n (hav.trans hdv.symm)
          subst d
          exact hA.variable_unique a j k ha hd
        · obtain ⟨a, _ha, hav⟩ := MvPolynomial.mem_vars_rename (freshMaskOldSlot n) (A j) hjo
          rw [← hav] at hkf
          exact (flattenedFreshMaskMultiplier_vars_no_old n b (tag k) a hkf).elim
      · rcases Finset.mem_union.mp hk' with hko | hkf
        · obtain ⟨a, _ha, hav⟩ := MvPolynomial.mem_vars_rename (freshMaskOldSlot n) (A k) hko
          rw [← hav] at hjf
          exact (flattenedFreshMaskMultiplier_vars_no_old n b (tag j) a hjf).elim
        · obtain ⟨he, hn⟩ := flattenedFreshMaskMultiplier_vars_collision n b (tag j) (tag k) v hjf hkf
          exact htag j k he hn

theorem PolynomialRowFamily.MonomialStructure.flattened_step {n r m : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m) (hF : F.MonomialStructure)
    (tag : Fin (m + 1) → Fin 3)
    (htag : ∀ j k, tag j = tag k → tag j ≠ 0 → j = k) :
    (F.flattenedMaskStep tag).MonomialStructure := by
  intro i
  let x := (Fintype.equivFin (MaskDescendant F tag)).symm i
  have he : (F.flattenedMaskStep tag).row i = flattenedMaskBranchRow (F.row x.val.1) tag x.val.2 := by
    funext k
    exact flattenedMaskStep_row F tag i k
  rw [he]
  exact PolynomialMonomialRow.flattened_branch _ (hF x.val.1) tag htag x.val.2

theorem initialMaskRowFamily_monomial (m : ℕ) :
    (initialMaskRowFamily (R := MvPolynomial (Fin 0) ℤ) m).MonomialStructure := by
  intro i
  constructor
  · intro k
    let U := ((Fintype.equivFin (NonemptyColumnSubset (m + 1))).symm i).val
    change (if k ∈ U then (1 : MvPolynomial (Fin 0) ℤ) else 0) = 0 ∨
      CoefficientOneMonomial (if k ∈ U then (1 : MvPolynomial (Fin 0) ℤ) else 0)
    split_ifs
    · exact Or.inr (coefficientOneMonomial_one _)
    · exact Or.inl rfl
  · intro v
    exact isEmptyElim v

end Hindman168
