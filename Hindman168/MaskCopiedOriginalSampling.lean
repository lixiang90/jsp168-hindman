import Hindman168.MaskGeneratedShiftLengths
import Hindman168.MaskCopiedStagePrefactors

/-! A concrete instance of the copied-row sampling contract. Every original
column uses its actual chain-pivot harmonic law; all direction branches use
the common quotient interval [0,floor(R/(J M(p)))). The sampling budget is
the paper's V at the gap, rather than an assumed error or moment bound. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def maskOriginalColumnDecode (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (j : MaskCopiedIndex m gap t) :
    PolynomialRowFamily.AdditiveColumn (maskGeneratedRowDataFamily m gap t).target m :=
  (Fintype.equivFin (PolynomialRowFamily.AdditiveColumn (maskGeneratedRowDataFamily m gap t).target m)).symm j

noncomputable def maskOriginalHarmonic (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) : Finset (MaskCopiedIndex m gap t) :=
  Finset.univ.filter (fun j => match maskOriginalColumnDecode m gap t j with
    | .inl _ => True
    | .inr _ => False)

theorem maskOriginalHarmonic_inl (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (col : Fin (m + 1)) :
    Fintype.equivFin (PolynomialRowFamily.AdditiveColumn (maskGeneratedRowDataFamily m gap t).target m)
      (.inl col) ∈ maskOriginalHarmonic m gap t := by
  simp [maskOriginalHarmonic, maskOriginalColumnDecode]

theorem maskOriginalHarmonic_not_inr (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m)))
    (kb : Fin (Fintype.card (PolynomialRowFamily.OffTargetRow
      (maskGeneratedRowDataFamily m gap t).target)) × Bool) :
    Fintype.equivFin (PolynomialRowFamily.AdditiveColumn (maskGeneratedRowDataFamily m gap t).target m)
      (.inr kb) ∉ maskOriginalHarmonic m gap t := by
  simp [maskOriginalHarmonic, maskOriginalColumnDecode]

noncomputable def maskOriginalIndex (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (w : ℕ) (j : MaskCopiedIndex m gap t) : Fin N :=
  match maskOriginalColumnDecode m gap t j with
  | .inl col => ⟨(C w).pivot col, Finset.mem_range.mp (hC w col (by simp [Chain.block]))⟩
  | .inr _ => gap w

theorem maskOriginalIndex_inl (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (w : ℕ) (col : Fin (m + 1)) :
    (maskOriginalIndex m gap C hC t w
      (Fintype.equivFin (PolynomialRowFamily.AdditiveColumn (maskGeneratedRowDataFamily m gap t).target m)
        (.inl col))).val = (C w).pivot col := by
  simp only [maskOriginalIndex, maskOriginalColumnDecode, Equiv.symm_apply_apply]

theorem maskGeneratedShiftLower_sampling_growth (m : ℕ) {N : ℕ} (gap : ℕ → Fin N) (J : ℕ) :
    PowerDominates atTop (fun w => (maskGeneratedShiftLower m gap J w : ℝ))
      (fun w => (samplingSize 0 ((maskGeneratedMaster m gap).auxiliary w (gap w).val)
        0 ((maskGeneratedMaster m gap).auxiliary w (gap w).val) : ℝ)) := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  apply (hF.quotient_sqrt_sampling_growth gap (J + maskRowDirectionSizeExponent m)
    (Eventually.of_forall (fun _ => le_rfl))).mono_right
  exact Eventually.of_forall (fun _ => ⟨Nat.cast_nonneg _, by exact_mod_cast Nat.sqrt_le_self _⟩)

noncomputable def maskOriginalSampling (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
    (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col) : MaskCopiedSampling m N := by
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
    harmonic := maskOriginalHarmonic m gap t
    index := maskOriginalIndex m gap C hC t
    minimum := fun w _ => maskGeneratedShiftLower m gap J w
    location := fun _ _ _ => 0
    length := fun w x _ => maskGeneratedShiftLength m gap t J w x
    harmonic_budget := ?_
    length_growth := fun _ _ => maskGeneratedShiftLower_sampling_growth m gap J
    length_lower := Eventually.of_forall (fun w x hx _ _ =>
      maskGeneratedShiftLower_le_length m gap t J hJ w x hx) }
  filter_upwards [hgap] with w hw
  intro j hj
  cases hd : maskOriginalColumnDecode m gap t j with
  | inl col =>
    simpa only [maskOriginalIndex, hd] using hF.auxiliary_monotone w (hw col)
  | inr kb =>
    simp only [maskOriginalHarmonic, Finset.mem_filter, hd, and_false] at hj

end Hindman168
