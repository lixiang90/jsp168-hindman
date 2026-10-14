import Hindman168.RootSmoothedAdditiveRows

/-! Exact counts for the canonical old non-target copies. For each of b
non-target rows its own branch is fixed false, leaving b-1 free Boolean
choices. This includes b=0 without a separate asymptotic convention. -/

namespace Hindman168

open scoped BigOperators Classical

abbrev AdditiveNonRootCopy (b : ℕ) :=
  {r : CopiedReplicaCubeRow (additiveRowAssigned b) // r.val.1 ≠ none}

noncomputable def additiveBranchFibreEquiv {b : ℕ} (k : Fin b) :
    {η : Fin b → Bool // η k = false} ≃ ({j : Fin b // j ≠ k} → Bool) where
  toFun η j := η.val j.val
  invFun θ := ⟨fun j => if h : j = k then false else θ ⟨j, h⟩, by simp⟩
  left_inv η := by
    apply Subtype.ext
    funext j
    by_cases h : j = k
    · subst j
      simpa using η.property.symm
    · simp only [dif_neg h]
  right_inv θ := by
    funext j
    simp only [dif_neg j.property]

theorem additiveBranchFibre_card {b : ℕ} (k : Fin b) :
    Fintype.card {η : Fin b → Bool // η k = false} = 2 ^ (b - 1) := by
  rw [Fintype.card_congr (additiveBranchFibreEquiv k), Fintype.card_fun, Fintype.card_bool]
  have hc : Fintype.card {j : Fin b // j ≠ k} = b - 1 := by
    change Fintype.card {j : Fin b // ¬ j = k} = b - 1
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
  rw [hc]

noncomputable def additiveNonRootCopyFromBranches {b : ℕ}
    (p : Σ k : Fin b, {η : Fin b → Bool // η k = false}) : AdditiveNonRootCopy b :=
  ⟨⟨(some (additiveRowAssigned b p.1), p.2.val), by
    intro k hk
    have he : p.1 = k := additiveRowAssigned_injective b (Option.some.inj hk)
    exact he ▸ p.2.property⟩, by simp⟩

theorem additiveNonRootCopyFromBranches_injective (b : ℕ) :
    Function.Injective (@additiveNonRootCopyFromBranches b) := by
  rintro ⟨k, η⟩ ⟨l, θ⟩ he
  have hk : k = l := additiveRowAssigned_injective b (Option.some.inj
    (congrArg (fun r : AdditiveNonRootCopy b => r.val.val.1) he))
  subst l
  have hη : η.val = θ.val := congrArg (fun r : AdditiveNonRootCopy b => r.val.val.2) he
  exact congrArg (Sigma.mk k) (Subtype.ext hη)

theorem additiveNonRootCopyFromBranches_surjective (b : ℕ) :
    Function.Surjective (@additiveNonRootCopyFromBranches b) := by
  intro r
  cases hb : r.val.val.1 with
  | none => exact False.elim (r.property hb)
  | some a =>
    obtain ⟨k, hk⟩ := additiveRowAssigned_surjective b a
    have hown : r.val.val.2 k = false := r.val.property k (hb.trans (congrArg some hk).symm)
    refine ⟨⟨k, ⟨r.val.val.2, hown⟩⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext ((congrArg some hk).trans hb.symm) rfl

theorem additiveNonRootCopy_card (b : ℕ) :
    Fintype.card (AdditiveNonRootCopy b) = b * 2 ^ (b - 1) := by
  rw [← Fintype.card_congr (Equiv.ofBijective (@additiveNonRootCopyFromBranches b)
    ⟨additiveNonRootCopyFromBranches_injective b, additiveNonRootCopyFromBranches_surjective b⟩)]
  simp only [Fintype.card_sigma, additiveBranchFibre_card, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end Hindman168
