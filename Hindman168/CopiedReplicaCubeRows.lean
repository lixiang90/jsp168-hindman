import Hindman168.ReplicaCubeResponseConstants

/-!
# The actual canonical rows after prediction direction duplication

A row copy selects one of two independent variables for each direction.
The branch in the row's own zero-response direction is fixed to false:
changing that branch would repeat the same form, not create another row.
Different base rows are separated on the original shifts. Copies of one
base row are separated on a direction with nonzero fixed response factor.
-/

namespace Hindman168

open scoped BigOperators Classical

abbrev CopiedReplicaCubeColumn (b d h : ℕ) := ReplicaCubeColumn b d ⊕ (Fin h × Bool)

abbrev CopiedReplicaCubeRow {b d h : ℕ} (dir : Fin h → Fin b × CubeVertex d) :=
  {v : ReplicaCubeRow b d × (Fin h → Bool) // ∀ i, v.1 = some (dir i) → v.2 i = false}

noncomputable def copiedReplicaCubeCoefficient {R : Type*} [CommRing R] {b d h : ℕ}
    (M : Fin b → R) (dir : Fin h → Fin b × CubeVertex d)
    (r : CopiedReplicaCubeRow dir) (col : CopiedReplicaCubeColumn b d h) : R :=
  match col with
  | .inl col => replicaCubeCoefficient M r.val.1 col
  | .inr (i, bit) => if bit = r.val.2 i then
      (replicaCubeResponseConstant (dir i).1 (dir i).2 r.val.1 : R) * M (dir i).1 else 0

theorem copiedReplicaCubeCoefficient_anchor {R : Type*} [CommRing R] {b d h : ℕ}
    (M : Fin b → R) (dir : Fin h → Fin b × CubeVertex d) (r : CopiedReplicaCubeRow dir) :
    copiedReplicaCubeCoefficient M dir r (.inl none) = 1 := rfl

theorem copiedReplicaCubeCoefficient_intCast {R : Type*} [CommRing R] {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (r : CopiedReplicaCubeRow dir)
    (col : CopiedReplicaCubeColumn b d h) :
    ((copiedReplicaCubeCoefficient M dir r col : ℤ) : R) =
      copiedReplicaCubeCoefficient (fun q => (M q : R)) dir r col := by
  cases col with
  | inl col => exact replicaCubeCoefficient_intCast M r.val.1 col
  | inr col =>
    rcases col with ⟨i, bit⟩
    simp only [copiedReplicaCubeCoefficient]
    split_ifs
    · exact Int.cast_mul _ _
    · exact Int.cast_zero

theorem copiedReplicaCubeCoefficient_distinguishing {R : Type*} [CommRing R] [IsDomain R] {b d h : ℕ}
    (M : Fin b → R) (hM : ∀ q, M q ≠ 0) (dir : Fin h → Fin b × CubeVertex d)
    (hc : ∀ i r, r ≠ some (dir i) →
      (replicaCubeResponseConstant (dir i).1 (dir i).2 r : R) ≠ 0)
    (r s : CopiedReplicaCubeRow dir) (hrs : r ≠ s) :
    ∃ col, copiedReplicaCubeCoefficient M dir r col ≠ copiedReplicaCubeCoefficient M dir s col := by
  by_cases hbase : r.val.1 = s.val.1
  · have hchoices : r.val.2 ≠ s.val.2 := by
      intro he
      exact hrs (Subtype.ext (Prod.ext hbase he))
    have hex : ∃ i, r.val.2 i ≠ s.val.2 i := by
      by_contra! he
      exact hchoices (funext he)
    obtain ⟨i, hi⟩ := hex
    have hactive : r.val.1 ≠ some (dir i) := by
      intro he
      exact hi ((r.property i he).trans (s.property i (hbase.symm.trans he)).symm)
    refine ⟨.inr (i, r.val.2 i), ?_⟩
    simpa only [copiedReplicaCubeCoefficient, ite_true, if_neg hi] using
      mul_ne_zero (hc i r.val.1 hactive) (hM (dir i).1)
  · obtain ⟨col, hcol⟩ := replicaCubeCoefficient_distinguishing M hM r.val.1 s.val.1 hbase
    exact ⟨.inl col, hcol⟩

theorem copiedReplicaCubeCoefficient_pair_independent {R : Type*} [CommRing R] [IsDomain R]
    {b d h : ℕ} (M : Fin b → R) (hM : ∀ q, M q ≠ 0)
    (dir : Fin h → Fin b × CubeVertex d)
    (hc : ∀ i r, r ≠ some (dir i) →
      (replicaCubeResponseConstant (dir i).1 (dir i).2 r : R) ≠ 0)
    (r s : CopiedReplicaCubeRow dir) (hrs : r ≠ s) :
    LinearIndependent R ![copiedReplicaCubeCoefficient M dir r, copiedReplicaCubeCoefficient M dir s] :=
  anchored_rows_pair_independent _ _ (.inl none) rfl rfl
    (copiedReplicaCubeCoefficient_distinguishing M hM dir hc r s hrs)

noncomputable def copiedReplicaCubeFinCoefficient {b d h : ℕ} (M : Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (r : CopiedReplicaCubeRow dir)
    (j : Fin (Fintype.card (CopiedReplicaCubeColumn b d h))) : ℤ :=
  copiedReplicaCubeCoefficient M dir r ((Fintype.equivFin (CopiedReplicaCubeColumn b d h)).symm j)

theorem copiedReplicaCubeFinCoefficient_primitive {p b d h : ℕ} (hp : p.Prime)
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (r : CopiedReplicaCubeRow dir) :
    ∃ j, (copiedReplicaCubeFinCoefficient M dir r j : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨Fintype.equivFin (CopiedReplicaCubeColumn b d h) (.inl none), ?_⟩
  simp only [copiedReplicaCubeFinCoefficient, Equiv.symm_apply_apply,
    copiedReplicaCubeCoefficient_anchor, Int.cast_one, ne_eq, one_ne_zero, not_false_eq_true]

theorem copiedReplicaCubeFinCoefficient_pair_independent {p b d h : ℕ} (hp : p.Prime)
    (M : Fin b → ℤ) (hM : ∀ q, (M q : ZMod p) ≠ 0)
    (dir : Fin h → Fin b × CubeVertex d)
    (hc : ∀ i r, r ≠ some (dir i) →
      (replicaCubeResponseConstant (dir i).1 (dir i).2 r : ZMod p) ≠ 0)
    (r s : CopiedReplicaCubeRow dir) (hrs : r ≠ s) :
    LinearIndependent (ZMod p)
      ![(fun j => (copiedReplicaCubeFinCoefficient M dir r j : ZMod p)),
        (fun j => (copiedReplicaCubeFinCoefficient M dir s j : ZMod p))] := by
  letI : Fact p.Prime := ⟨hp⟩
  let root := Fintype.equivFin (CopiedReplicaCubeColumn b d h) (.inl none)
  apply anchored_rows_pair_independent _ _ root
  · simp only [root, copiedReplicaCubeFinCoefficient, Equiv.symm_apply_apply,
      copiedReplicaCubeCoefficient_anchor, Int.cast_one]
  · simp only [root, copiedReplicaCubeFinCoefficient, Equiv.symm_apply_apply,
      copiedReplicaCubeCoefficient_anchor, Int.cast_one]
  · obtain ⟨col, hcol⟩ := copiedReplicaCubeCoefficient_distinguishing
      (fun q => (M q : ZMod p)) hM dir hc r s hrs
    refine ⟨Fintype.equivFin (CopiedReplicaCubeColumn b d h) col, ?_⟩
    simpa only [copiedReplicaCubeFinCoefficient, Equiv.symm_apply_apply,
      copiedReplicaCubeCoefficient_intCast] using hcol

noncomputable def replicaRootCopy {b d h : ℕ} (dir : Fin h → Fin b × CubeVertex d)
    (η : Fin h → Bool) : CopiedReplicaCubeRow dir :=
  ⟨(none, η), by intro i he; cases he⟩

theorem replicaRootCopy_injective {b d h : ℕ} (dir : Fin h → Fin b × CubeVertex d) :
    Function.Injective (replicaRootCopy dir) := by
  intro η θ he
  exact congrArg (fun r : CopiedReplicaCubeRow dir => r.val.2) he

end Hindman168
