import Hindman168.MaskGeneratedAdditiveResidues
import Hindman168.ReplicaCubePolynomialTests

/-! The actual copied coefficient array is defined at every prime tuple.
On the original good tuples it equals the additive-elimination data.
Its primitive-row certificate does not exclude polynomial bad primes. -/

namespace Hindman168.PolynomialRowFamily

open scoped BigOperators Classical

variable {n r m : ℕ}

abbrev AdditiveCopy {r : ℕ} (target : Fin r) :=
  CopiedReplicaCubeRow (additiveRowAssigned (Fintype.card (OffTargetRow target)))

abbrev AdditiveColumn {r : ℕ} (target : Fin r) (m : ℕ) :=
  AdditiveCopiedColumn (Fintype.card (OffTargetRow target)) (m + 1)

noncomputable def copiedIntegerCoefficient
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target : Fin r) (i : AdditiveCopy target) (j : AdditiveColumn target m) : ℤ :=
  match j with
  | .inl k => F.normalizedIntegerRow x c (additiveIndexEquiv target i.val.1) k
  | .inr (k, bit) => if bit = i.val.2 k then
      F.normalizedIntegerLinearForm x c (additiveIndexEquiv target i.val.1)
        (F.integerTranslation master w c x target (additiveIndexEquiv target (some (additiveRowAssigned _ k))))
      else 0

noncomputable def copiedFinIntegerCoefficient
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target : Fin r) (i : AdditiveCopy target)
    (j : Fin (Fintype.card (AdditiveColumn target m))) : ℤ :=
  F.copiedIntegerCoefficient master w c x target i
    ((Fintype.equivFin (AdditiveColumn target m)).symm j)

theorem AdditiveEliminationConditions.copiedCoefficient_eq
    {F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m}
    {master : MasterParameterFamily} {w : ℕ} {c : Fin (m + 1) → ℕ}
    {x : Fin n → ℕ} {target : Fin r}
    (H : F.AdditiveEliminationConditions master w c x target)
    (i : AdditiveCopy target) (j : AdditiveColumn target m) :
    H.data.copiedCoefficient i j = F.copiedIntegerCoefficient master w c x target i j := by
  cases j with
  | inl k => exact H.coefficient_eq _ k
  | inr kb =>
    simp only [AdditiveRowData.copiedCoefficient, copiedIntegerCoefficient]
    split_ifs
    · exact H.response_eq _ _
    · rfl

theorem AdditiveEliminationConditions.copiedFinCoefficient_eq
    {F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m}
    {master : MasterParameterFamily} {w : ℕ} {c : Fin (m + 1) → ℕ}
    {x : Fin n → ℕ} {target : Fin r}
    (H : F.AdditiveEliminationConditions master w c x target)
    (i : AdditiveCopy target) (j : Fin (Fintype.card (AdditiveColumn target m))) :
    H.data.copiedFinCoefficient i j = F.copiedFinIntegerCoefficient master w c x target i j :=
  H.copiedCoefficient_eq i _

theorem copiedFinIntegerCoefficient_primitive
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target : Fin r) {V B K : ℕ}
    (hd : F.IntegerRowDirectionConditions master w c x target V B K)
    (p : ℕ) (hp : p.Prime) (hpV : p ≤ V) (i : AdditiveCopy target) :
    ∃ j, (F.copiedFinIntegerCoefficient master w c x target i j : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  let a := F.normalizationAnchor (additiveIndexEquiv target i.val.1)
  refine ⟨Fintype.equivFin (AdditiveColumn target m) (.inl a), ?_⟩
  simpa only [copiedFinIntegerCoefficient, Equiv.symm_apply_apply, copiedIntegerCoefficient] using
    (hd.anchor_units (additiveIndexEquiv target i.val.1) p hp.pos hpV).ne_zero

theorem copiedFinIntegerCoefficient_pair_independent
    {F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m}
    {master : MasterParameterFamily} {w : ℕ} {c : Fin (m + 1) → ℕ}
    {x : Fin n → ℕ} {target : Fin r} {V B K : ℕ}
    (H : F.AdditiveEliminationConditions master w c x target)
    (hd : F.IntegerRowDirectionConditions master w c x target V B K)
    (p : ℕ) (hp : p.Prime) (hwp : w < p) (hpV : p ≤ V)
    (havoid : ∀ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (x j : ZMod p)) f ≠ 0)
    (i j : AdditiveCopy target) (hij : i ≠ j) :
    LinearIndependent (ZMod p)
      ![(fun k => (F.copiedFinIntegerCoefficient master w c x target i k : ZMod p)),
        (fun k => (F.copiedFinIntegerCoefficient master w c x target j k : ZMod p))] := by
  simpa only [H.copiedFinCoefficient_eq] using
    (H.residue_conditions hd p hp hwp hpV havoid).copiedFin_pair_independent hp i j hij

theorem catalog_nonzero_of_not_squarefree_bad
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m) (target : Fin r)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (x : Fin n → ℕ) (p : S)
    (hbad : ¬ squarefreeCRTBadEvent S hS (F.catalog target)
      (fun j => (x j : ZMod (squarefreeCRTModulus S))) p) :
    ∀ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod (p : ℕ))) (fun j => (x j : ZMod (p : ℕ))) f ≠ 0 := by
  intro f hf
  rw [MvPolynomial.eval₂_eq_eval_map]
  exact polynomial_nonzero_of_not_squarefree_bad S hS (F.catalog target) x p hbad f hf

end Hindman168.PolynomialRowFamily
