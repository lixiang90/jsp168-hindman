import Hindman168.AdditiveRowResidueIndependence
import Hindman168.MaskGeneratedAdditiveElimination

/-! Actual generated rows satisfy the copied-form residue conditions.
The rough-prime exceptions are the existing fixed nonzero polynomial catalogue. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

namespace PolynomialRowFamily.AdditiveEliminationConditions

variable {n r m : ℕ} {F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m}
  {master : MasterParameterFamily} {w : ℕ} {c : Fin (m + 1) → ℕ}
  {x : Fin n → ℕ} {target : Fin r}

theorem coefficient_eq (H : F.AdditiveEliminationConditions master w c x target)
    (i : ReplicaCubeRow (Fintype.card (PolynomialRowFamily.OffTargetRow target)) 1)
    (j : Fin (m + 1)) :
    H.data.coefficient i j = F.normalizedIntegerRow x c (PolynomialRowFamily.additiveIndexEquiv target i) j := by
  have he := H.form_eq i (Pi.single j 1)
  rw [H.data.form_single] at he
  simpa [PolynomialRowFamily.normalizedIntegerLinearForm, Pi.single_apply] using he

theorem response_eq (H : F.AdditiveEliminationConditions master w c x target)
    (i : ReplicaCubeRow (Fintype.card (PolynomialRowFamily.OffTargetRow target)) 1)
    (k : Fin (Fintype.card (PolynomialRowFamily.OffTargetRow target))) :
    H.data.response i k = F.normalizedIntegerLinearForm x c
      (PolynomialRowFamily.additiveIndexEquiv target i)
      (F.integerTranslation master w c x target
        (PolynomialRowFamily.additiveIndexEquiv target (some (additiveRowAssigned _ k)))) := by
  unfold AdditiveRowData.response
  rw [H.form_eq]
  congr 1
  funext j
  exact H.direction_eq k j

theorem residue_conditions (H : F.AdditiveEliminationConditions master w c x target)
    {V B K : ℕ} (hd : F.IntegerRowDirectionConditions master w c x target V B K)
    (p : ℕ) (hp : p.Prime) (hwp : w < p) (hpV : p ≤ V)
    (havoid : ∀ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (x j : ZMod p)) f ≠ 0) :
    H.data.ResidueConditions p := by
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro i
    refine ⟨F.normalizationAnchor (PolynomialRowFamily.additiveIndexEquiv target i), ?_⟩
    rw [H.coefficient_eq]
    exact (hd.anchor_units _ p hp.pos hpV).ne_zero
  · intro k i hi
    rw [H.response_eq]
    apply (hd.rough_units p hp hwp havoid).1
      (PolynomialRowFamily.additiveIndexEquiv target (some (additiveRowAssigned _ k)))
      (PolynomialRowFamily.additiveIndexEquiv_assigned_ne target k)
    intro he
    exact hi ((PolynomialRowFamily.additiveIndexEquiv target).injective he)

end PolynomialRowFamily.AdditiveEliminationConditions

structure PolynomialRowFamily.AdditiveResidueEliminationConditions {n r m : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target : Fin r) (V : ℕ) where
  elimination : F.AdditiveEliminationConditions master w c x target
  residues : ∀ p : ℕ, p.Prime → w < p → p ≤ V →
    (∀ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (x j : ZMod p)) f ≠ 0) →
    elimination.data.ResidueConditions p

theorem maskGenerated_additive_residue_elimination_data (m : ℕ) {N : ℕ}
    (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ k, 0 < a k)
    (C : ℕ → Chain (m + 1)) (hC : ∀ w k, (C w).block k ⊆ Finset.range N) :
    ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)),
      ∀ x ∈ (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
        ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper).support,
      predictionLocalPrimeGoodEvent (maskGeneratedMaster m gap)
        ((maskGeneratedRowDataFamily m gap t).rows.catalog (maskGeneratedRowDataFamily m gap t).target)
        ((maskGeneratedRowDataFamily m gap t).rows.denominator (maskGeneratedRowDataFamily m gap t).target) w x →
      Nonempty ((maskGeneratedRowDataFamily m gap t).rows.AdditiveResidueEliminationConditions
        (maskGeneratedMaster m gap) w (masterColumnCoefficient N a (fun w => (C w).block) w) x
        (maskGeneratedRowDataFamily m gap t).target
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val)) := by
  filter_upwards [maskGenerated_additive_elimination_data m gap a ha C hC,
    maskGenerated_chain_integer_row_directions m gap a ha C hC] with w he hd
  intro t x hx hg
  obtain ⟨H⟩ := he t x hg
  exact ⟨{
    elimination := H
    residues := fun p hp hwp hpV havoid => H.residue_conditions (hd t x hx hg) p hp hwp hpV havoid }⟩

namespace PolynomialRowFamily.AdditiveResidueEliminationConditions

variable {n r m : ℕ} {F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m}
  {master : MasterParameterFamily} {w : ℕ} {c : Fin (m + 1) → ℕ}
  {x : Fin n → ℕ} {target : Fin r} {V : ℕ}

theorem copiedFin_primitive (H : F.AdditiveResidueEliminationConditions master w c x target V)
    (p : ℕ) (hp : p.Prime) (hwp : w < p) (hpV : p ≤ V)
    (havoid : ∀ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (x j : ZMod p)) f ≠ 0)
    (i : CopiedReplicaCubeRow (additiveRowAssigned (Fintype.card (PolynomialRowFamily.OffTargetRow target)))) :
    ∃ j, (H.elimination.data.copiedFinCoefficient i j : ZMod p) ≠ 0 :=
  (H.residues p hp hwp hpV havoid).copiedFin_primitive i

theorem copiedFin_pair_independent (H : F.AdditiveResidueEliminationConditions master w c x target V)
    (p : ℕ) (hp : p.Prime) (hwp : w < p) (hpV : p ≤ V)
    (havoid : ∀ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (x j : ZMod p)) f ≠ 0)
    (i j : CopiedReplicaCubeRow (additiveRowAssigned (Fintype.card (PolynomialRowFamily.OffTargetRow target))))
    (hij : i ≠ j) :
    LinearIndependent (ZMod p)
      ![(fun k => (H.elimination.data.copiedFinCoefficient i k : ZMod p)),
        (fun k => (H.elimination.data.copiedFinCoefficient j k : ZMod p))] :=
  (H.residues p hp hwp hpV havoid).copiedFin_pair_independent hp i j hij

theorem copiedFin_nonprimitive_exception (H : F.AdditiveResidueEliminationConditions master w c x target V)
    (p : ℕ) (hp : p.Prime) (hwp : w < p) (hpV : p ≤ V)
    (i : CopiedReplicaCubeRow (additiveRowAssigned (Fintype.card (PolynomialRowFamily.OffTargetRow target))))
    (hbad : ¬ ∃ j, (H.elimination.data.copiedFinCoefficient i j : ZMod p) ≠ 0) :
    ∃ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (x j : ZMod p)) f = 0 := by
  by_contra h
  have havoid : ∀ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (x j : ZMod p)) f ≠ 0 := by
    intro f hf hz
    exact h ⟨f, hf, hz⟩
  exact hbad (H.copiedFin_primitive p hp hwp hpV havoid i)

theorem copiedFin_nonindependent_exception (H : F.AdditiveResidueEliminationConditions master w c x target V)
    (p : ℕ) (hp : p.Prime) (hwp : w < p) (hpV : p ≤ V)
    (i j : CopiedReplicaCubeRow (additiveRowAssigned (Fintype.card (PolynomialRowFamily.OffTargetRow target))))
    (hij : i ≠ j)
    (hbad : ¬ LinearIndependent (ZMod p)
      ![(fun k => (H.elimination.data.copiedFinCoefficient i k : ZMod p)),
        (fun k => (H.elimination.data.copiedFinCoefficient j k : ZMod p))]) :
    ∃ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun k => (x k : ZMod p)) f = 0 := by
  by_contra h
  have havoid : ∀ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun k => (x k : ZMod p)) f ≠ 0 := by
    intro f hf hz
    exact h ⟨f, hf, hz⟩
  exact hbad (H.copiedFin_pair_independent p hp hwp hpV havoid i j hij)

end PolynomialRowFamily.AdditiveResidueEliminationConditions

theorem maskGenerated_additive_copied_column_bound (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :
    Fintype.card (AdditiveCopiedColumn
      (Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target))
      (m + 1)) ≤ (m + 1) + 2 * maskRowCountBound m := by
  rw [additiveCopiedColumn_card]
  have h := maskGenerated_additive_dimension_le m gap t
  omega

end Hindman168
