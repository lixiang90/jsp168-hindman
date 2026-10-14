import Hindman168.NativePieceFiniteSelection
import Hindman168.InjectiveOptionSelection
import Hindman168.CompleteResidueCellPartition

namespace Hindman168
open scoped BigOperators Classical
universe u v

theorem complete_cell_piece_label_injective (M : ℕ) :
    Function.Injective (fun c : ℤ × Fin M => (c.1, (c.2.val : ℤ))) := by
  intro c c' he
  apply Prod.ext
  · exact (Prod.mk.inj he).1
  · apply Fin.ext
    exact_mod_cast (Prod.mk.inj he).2

/-- Assemble actual unit native recipes from a fixed finite list on good
complete cells, choosing independently on every stage and cell. Zero is
used elsewhere. Local correlator existence is an explicit input, not an
inverse theorem axiom. Geometry is required only on the selected stages. -/
theorem native_good_cell_family_assembly {s N : ℕ}
    (F : MasterParameterFamily) (gap : ℕ → Fin N) {ι : Type v} [Fintype ι] [Nonempty ι]
    (recipes : ι → ℕ → ℤ → ℝ)
    (hr : ∀ i, NativePieceRepresented.{u} s F gap (recipes i))
    (hb : ∀ i w y, |recipes i w y| ≤ 1)
    (M q : ℕ → ℕ) (A : Set ℕ)
    (hgeom : ∀ w ∈ A, 0 < M w ∧ 0 < q w ∧
      (F.modulus w : ℕ) = M w ∧ F.gap w (gap w).val = M w * q w)
    (C : (w : ℕ) → Finset (ℤ × Fin (M w)))
    (P : (w : ℕ) → C w → Prop) (f : ℕ → ℤ → ℝ) (γ : ℝ)
    (hlocal : ∀ w ∈ A, ∀ c : C w, P w c → ∃ i,
      γ ≤ finiteHaarMean (fun t : Fin (q w) =>
        f w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) *
          recipes i w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t))) :
    ∃ V : ℕ → ℤ → ℝ,
      NativePieceRepresented.{u} s F gap V ∧ (∀ w y, |V w y| ≤ 1) ∧
      (∀ w ∈ A, ∀ c : C w, P w c →
        γ ≤ finiteHaarMean (fun t : Fin (q w) =>
          f w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) *
            V w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t))) ∧
      (∀ w (c : C w), ¬ (w ∈ A ∧ P w c) → ∀ t : Fin (q w),
        V w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) = 0) ∧
      (∀ w y, y ∉ (C w).biUnion (fun c => intervalResidueSet
        (c.1 * (M w * q w : ℕ)) (M w * q w) (M w) c.2.val) → V w y = 0) ∧
      (∀ w, w ∉ A → ∀ y, V w y = 0) := by
  let label := fun w (c : C w) => (c.val.1, (c.val.2.val : ℤ))
  have hinj (w : ℕ) : Function.Injective (label w) := by
    intro c c' he
    exact Subtype.ext (complete_cell_piece_label_injective (M w) he)
  have hselectors := fun w => injective_admissible_option_selection (label w)
    (hinj w) (fun c => w ∈ A ∧ P w c)
  choose σ hσgood hσsome using hselectors
  let j := fun w (c : C w) => if h : w ∈ A ∧ P w c
    then (hlocal w h.1 c h.2).choose else Classical.arbitrary ι
  have hj (w : ℕ) (c : C w) (hc : w ∈ A ∧ P w c) :
      γ ≤ finiteHaarMean (fun t : Fin (q w) =>
        f w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) *
          recipes (j w c) w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t)) := by
    dsimp only [j]
    rw [dif_pos hc]
    exact (hlocal w hc.1 c hc.2).choose_spec
  let select := fun w p => (σ w p).map (j w)
  let piece := fun w y =>
    intervalResiduePiece (F.gap w (gap w).val) (F.modulus w : ℕ) y
  let V := fun w y => (select w (piece w y)).elim 0 (fun i => recipes i w y)
  have hstage (w : ℕ) (hw : w ∉ A) (p : ℤ × ℤ) : σ w p = none := by
    cases he : σ w p with
    | none => rfl
    | some c => exact False.elim (hw (hσsome w p c he).1.1)
  have hzeroStage (w : ℕ) (hw : w ∉ A) (y : ℤ) : V w y = 0 := by
    simp only [V, select, hstage w hw, Option.map_none, Option.elim_none]
  have hpoint (w : ℕ) (hw : w ∈ A) (c : C w) (t : Fin (q w)) :
      piece w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) = label w c := by
    obtain ⟨hM, hq, hm, hg⟩ := hgeom w hw
    dsimp only [piece, label]
    rw [hg, hm]
    exact (mem_intervalResidueSet_iff_piece (M w * q w) (M w) (Nat.mul_pos hM hq)
      c.val.1 c.val.2 _).mp (completeResidueCellPoint_mem _ _ _ hM _ _)
  refine ⟨V, nativePieceRepresented_piece_select F gap recipes hr select,
    piece_selected_family_unit F gap recipes hb select, ?_, ?_, ?_, hzeroStage⟩
  · intro w hw c hc
    have he (t : Fin (q w)) :
        V w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) =
          recipes (j w c) w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) := by
      simp only [V, select, hpoint w hw c t, hσgood w c ⟨hw, hc⟩,
        Option.map_some, Option.elim_some]
    simp_rw [he]
    exact hj w c ⟨hw, hc⟩
  · intro w c hc t
    by_cases hw : w ∈ A
    · have hn := admissible_option_selection_none (label w) (hinj w)
        (fun c => w ∈ A ∧ P w c) (σ w) (hσsome w) c hc
      simp only [V, select, hpoint w hw c t, hn, Option.map_none, Option.elim_none]
    · exact hzeroStage w hw _
  · intro w y hy
    by_cases hw : w ∈ A
    · have hn : σ w (piece w y) = none := by
        cases he : σ w (piece w y) with
        | none => rfl
        | some c =>
            have hl := (hσsome w (piece w y) c he).2
            obtain ⟨hM, hq, hm, hg⟩ := hgeom w hw
            have hp : intervalResiduePiece (M w * q w) (M w) y = label w c := by
              simpa only [piece, hm, hg] using hl.symm
            have hc := (mem_intervalResidueSet_iff_piece (M w * q w) (M w)
              (Nat.mul_pos hM hq) c.val.1 c.val.2 y).mpr hp
            exact False.elim (hy (Finset.mem_biUnion.mpr ⟨c.val, c.property, hc⟩))
      simp only [V, select, hn, Option.map_none, Option.elim_none]
    · exact hzeroStage w hw y

end Hindman168
