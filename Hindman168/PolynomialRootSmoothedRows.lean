import Hindman168.RootSmoothedAdditiveResidues
import Hindman168.PolynomialCopiedIntegerRows

/-! Root-smoothed coefficient arrays at every tuple, with certificates from
the actual normalized rows and their integer root direction. The rough-prime
exception catalogue is unchanged. -/

namespace Hindman168.PolynomialRowFamily

open scoped BigOperators Classical

variable {n r m : ℕ}

abbrev RootSmoothedCopy {r : ℕ} (target : Fin r) :=
  RootSmoothedAdditiveCopy (Fintype.card (OffTargetRow target))

abbrev RootSmoothedColumn {r : ℕ} (target : Fin r) (m : ℕ) :=
  RootSmoothedAdditiveColumn (Fintype.card (OffTargetRow target)) (m + 1)

noncomputable def rootSmoothedIntegerCoefficient
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target : Fin r) (i : RootSmoothedCopy target)
    (j : RootSmoothedColumn target m) : ℤ :=
  match j with
  | .inl k => F.copiedIntegerCoefficient master w c x target i.val.1 k
  | .inr bit => if bit = i.val.2 then
      F.normalizedIntegerLinearForm x c (additiveIndexEquiv target i.val.1.val.1)
        (F.rootIntegerTranslation master w c x target) else 0

noncomputable def rootSmoothedFinIntegerCoefficient
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target : Fin r) (i : RootSmoothedCopy target)
    (j : Fin (Fintype.card (RootSmoothedColumn target m))) : ℤ :=
  F.rootSmoothedIntegerCoefficient master w c x target i
    ((Fintype.equivFin (RootSmoothedColumn target m)).symm j)

namespace AdditiveEliminationConditions

variable {F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m}
  {master : MasterParameterFamily} {w : ℕ} {c : Fin (m + 1) → ℕ}
  {x : Fin n → ℕ} {target : Fin r}

theorem rootSmoothedCoefficient_eq (H : F.AdditiveEliminationConditions master w c x target)
    (i : RootSmoothedCopy target) (j : RootSmoothedColumn target m) :
    H.data.rootSmoothedCoefficient (F.rootIntegerTranslation master w c x target) i j =
      F.rootSmoothedIntegerCoefficient master w c x target i j := by
  cases j with
  | inl k => exact H.copiedCoefficient_eq _ k
  | inr bit =>
    simp only [AdditiveRowData.rootSmoothedCoefficient, rootSmoothedIntegerCoefficient]
    split_ifs
    · exact H.form_eq _ _
    · rfl

theorem rootSmoothedFinCoefficient_eq
    (H : F.AdditiveEliminationConditions master w c x target)
    (i : RootSmoothedCopy target) (j : Fin (Fintype.card (RootSmoothedColumn target m))) :
    H.data.rootSmoothedFinCoefficient (F.rootIntegerTranslation master w c x target) i j =
      F.rootSmoothedFinIntegerCoefficient master w c x target i j :=
  H.rootSmoothedCoefficient_eq i _

theorem root_residue_conditions (H : F.AdditiveEliminationConditions master w c x target)
    {V B K : ℕ} (hd : F.IntegerRowDirectionConditions master w c x target V B K)
    (p : ℕ) (hp : p.Prime) (hwp : w < p) (hpV : p ≤ V)
    (havoid : ∀ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (x j : ZMod p)) f ≠ 0) :
    H.data.RootResidueConditions (F.rootIntegerTranslation master w c x target) p := by
  refine ⟨H.residue_conditions hd p hp hwp hpV havoid, ?_⟩
  intro i hi
  rw [H.form_eq]
  apply (hd.rough_units p hp hwp havoid).2
  intro he
  apply hi
  exact (additiveIndexEquiv target).injective (he.trans (additiveIndexEquiv_root target).symm)

end AdditiveEliminationConditions

theorem rootSmoothedFinIntegerCoefficient_primitive
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target : Fin r) {V B K : ℕ}
    (hd : F.IntegerRowDirectionConditions master w c x target V B K)
    (p : ℕ) (hp : p.Prime) (hpV : p ≤ V) (i : RootSmoothedCopy target) :
    ∃ j, (F.rootSmoothedFinIntegerCoefficient master w c x target i j : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  let a := F.normalizationAnchor (additiveIndexEquiv target i.val.1.val.1)
  refine ⟨Fintype.equivFin (RootSmoothedColumn target m) (.inl (.inl a)), ?_⟩
  simpa only [rootSmoothedFinIntegerCoefficient, Equiv.symm_apply_apply,
    rootSmoothedIntegerCoefficient, copiedIntegerCoefficient] using
    (hd.anchor_units (additiveIndexEquiv target i.val.1.val.1) p hp.pos hpV).ne_zero

theorem rootSmoothedFinIntegerCoefficient_pair_independent
    {F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m}
    {master : MasterParameterFamily} {w : ℕ} {c : Fin (m + 1) → ℕ}
    {x : Fin n → ℕ} {target : Fin r} {V B K : ℕ}
    (H : F.AdditiveEliminationConditions master w c x target)
    (hd : F.IntegerRowDirectionConditions master w c x target V B K)
    (p : ℕ) (hp : p.Prime) (hwp : w < p) (hpV : p ≤ V)
    (havoid : ∀ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (x j : ZMod p)) f ≠ 0)
    (i j : RootSmoothedCopy target) (hij : i ≠ j) :
    LinearIndependent (ZMod p)
      ![(fun k => (F.rootSmoothedFinIntegerCoefficient master w c x target i k : ZMod p)),
        (fun k => (F.rootSmoothedFinIntegerCoefficient master w c x target j k : ZMod p))] := by
  simpa only [H.rootSmoothedFinCoefficient_eq] using
    (H.root_residue_conditions hd p hp hwp hpV havoid).fin_pair_independent hp i j hij

theorem rootSmoothedFinIntegerCoefficient_nonindependent_exception
    {F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m}
    {master : MasterParameterFamily} {w : ℕ} {c : Fin (m + 1) → ℕ}
    {x : Fin n → ℕ} {target : Fin r} {V B K : ℕ}
    (H : F.AdditiveEliminationConditions master w c x target)
    (hd : F.IntegerRowDirectionConditions master w c x target V B K)
    (p : ℕ) (hp : p.Prime) (hwp : w < p) (hpV : p ≤ V)
    (i j : RootSmoothedCopy target) (hij : i ≠ j)
    (hbad : ¬ LinearIndependent (ZMod p)
      ![(fun k => (F.rootSmoothedFinIntegerCoefficient master w c x target i k : ZMod p)),
        (fun k => (F.rootSmoothedFinIntegerCoefficient master w c x target j k : ZMod p))]) :
    ∃ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun k => (x k : ZMod p)) f = 0 := by
  by_contra h
  have havoid : ∀ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun k => (x k : ZMod p)) f ≠ 0 := by
    intro f hf hz
    exact h ⟨f, hf, hz⟩
  exact hbad (rootSmoothedFinIntegerCoefficient_pair_independent H hd p hp hwp hpV havoid i j hij)

end Hindman168.PolynomialRowFamily
