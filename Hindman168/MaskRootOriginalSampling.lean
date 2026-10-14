import Hindman168.MaskRootCopiedNormalized
import Hindman168.MaskOriginalSmoothedTerminal

/-! Concrete enlarged mixed law for the two independent root branches.
All original columns retain their actual pivot harmonic laws, old branches
retain [0,floor(R/(J M(x)))), and each root branch uses [0,R). The actual
quotient lower bound suffices for every uniform coordinate. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def maskRootColumnDecode (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (j : MaskRootCopiedIndex m gap t) :
    PolynomialRowFamily.RootSmoothedColumn (maskGeneratedRowDataFamily m gap t).target m :=
  (Fintype.equivFin (PolynomialRowFamily.RootSmoothedColumn
    (maskGeneratedRowDataFamily m gap t).target m)).symm j

noncomputable def maskRootHarmonic (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) : Finset (MaskRootCopiedIndex m gap t) :=
  Finset.univ.filter (fun j => match maskRootColumnDecode m gap t j with
    | .inl (.inl _) => True
    | _ => False)

theorem maskRootHarmonic_inl (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (col : Fin (m + 1)) :
    Fintype.equivFin (PolynomialRowFamily.RootSmoothedColumn (maskGeneratedRowDataFamily m gap t).target m)
      (.inl (.inl col)) ∈ maskRootHarmonic m gap t := by
  simp [maskRootHarmonic, maskRootColumnDecode]

theorem maskRootHarmonic_not_old (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m)))
    (kb : Fin (Fintype.card (PolynomialRowFamily.OffTargetRow
      (maskGeneratedRowDataFamily m gap t).target)) × Bool) :
    Fintype.equivFin (PolynomialRowFamily.RootSmoothedColumn (maskGeneratedRowDataFamily m gap t).target m)
      (.inl (.inr kb)) ∉ maskRootHarmonic m gap t := by
  simp [maskRootHarmonic, maskRootColumnDecode]

theorem maskRootHarmonic_not_root (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (bit : Bool) :
    Fintype.equivFin (PolynomialRowFamily.RootSmoothedColumn (maskGeneratedRowDataFamily m gap t).target m)
      (.inr bit) ∉ maskRootHarmonic m gap t := by
  simp [maskRootHarmonic, maskRootColumnDecode]

noncomputable def maskRootIndex (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (w : ℕ) (j : MaskRootCopiedIndex m gap t) : Fin N :=
  match maskRootColumnDecode m gap t j with
  | .inl (.inl col) => ⟨(C w).pivot col, Finset.mem_range.mp (hC w col (by simp [Chain.block]))⟩
  | _ => gap w

noncomputable def maskRootLength (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (J w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) (j : MaskRootCopiedIndex m gap t) : ℕ :=
  match maskRootColumnDecode m gap t j with
  | .inl _ => maskGeneratedShiftLength m gap t J w x
  | .inr _ => (maskGeneratedMaster m gap).gap w (gap w).val

theorem maskRootLength_lower (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J) (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (hx : maskGeneratedCopiedPrimeGood m gap t w x) (j : MaskRootCopiedIndex m gap t) :
    maskGeneratedShiftLower m gap J w ≤ maskRootLength m gap t J w x j := by
  have hl := maskGeneratedShiftLower_le_length m gap t J hJ w x hx
  unfold maskRootLength
  cases maskRootColumnDecode m gap t j with
  | inl col => exact hl
  | inr bit => exact hl.trans (Nat.div_le_self _ _)

noncomputable def maskRootOriginalSampling (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
    (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col) : MaskRootCopiedSampling m N := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  refine {
    gap := gap
    a := a
    positive := ha
    chain := C
    blocks := hC
    template := t
    budget := fun w => (maskGeneratedMaster m gap).auxiliary w (gap w).val
    budget_pos := Eventually.of_forall (fun w => (by decide : 1 ≤ 2).trans
      ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val))
    prime_budget := Eventually.of_forall (fun _ => le_rfl)
    harmonic := maskRootHarmonic m gap t
    index := maskRootIndex m gap C hC t
    minimum := fun w _ => maskGeneratedShiftLower m gap J w
    location := fun _ _ _ => 0
    length := maskRootLength m gap t J
    harmonic_budget := ?_
    length_growth := fun _ _ => maskGeneratedShiftLower_sampling_growth m gap J
    length_lower := Eventually.of_forall (fun w x hx j _ => maskRootLength_lower m gap t J hJ w x hx j) }
  filter_upwards [hgap] with w hw
  intro j hj
  cases hd : maskRootColumnDecode m gap t j with
  | inl col =>
    cases col with
    | inl col =>
      simpa only [maskRootIndex, hd] using hF.auxiliary_monotone w (hw col)
    | inr kb =>
      simp only [maskRootHarmonic, Finset.mem_filter, hd, and_false] at hj
  | inr bit =>
    simp only [maskRootHarmonic, Finset.mem_filter, hd, and_false] at hj

end Hindman168
