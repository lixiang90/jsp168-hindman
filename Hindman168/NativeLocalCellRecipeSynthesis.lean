import Hindman168.NativeGoodCellAssembly

namespace Hindman168
open NNReal
open scoped BigOperators Classical
universe u

/-- Local real observables on one actual native manifold, with one fixed
Lipschitz bound, produce a genuine stage family. The orbit parameters and
observable may vary freely on every selected complete cell. -/
theorem native_local_cell_recipe_synthesis {s N : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : MasterParameterFamily) (gap : ℕ → Fin N)
    (M q : ℕ → ℕ) (A : Set ℕ)
    (hgeom : ∀ w ∈ A, 0 < M w ∧ 0 < q w ∧
      (F.modulus w : ℕ) = M w ∧ F.gap w (gap w).val = M w * q w)
    (C : (w : ℕ) → Finset (ℤ × Fin (M w))) (P : (w : ℕ) → C w → Prop)
    (f : ℕ → ℤ → ℝ) (γ : ℝ) (Lip : ℝ≥0) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    (∀ w ∈ A, ∀ c : C w, P w c →
      ∃ (obs : C(D.G ⧸ D.Γ, ℝ)) (g x : D.G),
        (∀ z, |obs z| ≤ 1) ∧ LipschitzWith Lip obs ∧
        γ ≤ finiteHaarMean (fun t : Fin (q w) =>
          f w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) *
            obs (pieceLinearOrbit D.Γ (M w) (fun _ : Unit => g) (fun _ => x) ()
              (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t)))) →
    ∃ recipe : ℕ → ℤ → ℝ,
      nativePieceOn D F gap recipe ∧ (∀ w y, |recipe w y| ≤ 1) ∧
      (∀ w ∈ A, ∀ c : C w, P w c →
        γ ≤ finiteHaarMean (fun t : Fin (q w) =>
          f w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) *
            recipe w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t))) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro hlocal
  have hall : ∀ w (c : C w), ∃ (obs : C(D.G ⧸ D.Γ, ℝ)) (g x : D.G),
      (∀ z, |obs z| ≤ 1) ∧ LipschitzWith Lip obs ∧
      (w ∈ A ∧ P w c → γ ≤ finiteHaarMean (fun t : Fin (q w) =>
        f w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) *
          obs (pieceLinearOrbit D.Γ (M w) (fun _ : Unit => g) (fun _ => x) ()
            (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t)))) := by
    intro w c
    by_cases hc : w ∈ A ∧ P w c
    · obtain ⟨obs, g, x, hb, hl, hcorr⟩ := hlocal w hc.1 c hc.2
      exact ⟨obs, g, x, hb, hl, fun _ => hcorr⟩
    · refine ⟨ContinuousMap.const (D.G ⧸ D.Γ) (0 : ℝ), 1, 1, ?_, ?_, fun h => False.elim (hc h)⟩
      · intro z
        simp only [ContinuousMap.const_apply, abs_zero, zero_le_one]
      · change LipschitzWith Lip (fun _ : D.G ⧸ D.Γ => (0 : ℝ))
        exact (LipschitzWith.const (0 : ℝ)).weaken (show 0 ≤ Lip from zero_le)
  choose obs g x hb hl hcorr using hall
  let label := fun w (c : C w) => (c.val.1, (c.val.2.val : ℤ))
  have hinj (w : ℕ) : Function.Injective (label w) := by
    intro c c' he
    exact Subtype.ext (complete_cell_piece_label_injective (M w) he)
  choose σ hσgood _hσsome using
    (fun w => injective_admissible_option_selection (label w) (hinj w) (fun c => w ∈ A ∧ P w c))
  let obs' := fun w p => (σ w p).elim (ContinuousMap.const _ 0) (obs w)
  let g' := fun w p => (σ w p).elim 1 (g w)
  let x' := fun w p => (σ w p).elim 1 (x w)
  let recipe := piecewiseLinearNilsequence D.Γ F gap obs' g' x'
  have hobs (w : ℕ) (p : ℤ × ℤ) (z : D.G ⧸ D.Γ) : |obs' w p z| ≤ 1 := by
    cases hs : σ w p with
    | none => simp only [obs', hs, Option.elim_none, ContinuousMap.const_apply, abs_zero, zero_le_one]
    | some c => simpa only [obs', hs, Option.elim_some] using hb w c z
  have hLip (w : ℕ) (p : ℤ × ℤ) : LipschitzWith Lip (obs' w p) := by
    cases hs : σ w p with
    | none =>
        simp only [obs', hs, Option.elim_none]
        change LipschitzWith Lip (fun _ : D.G ⧸ D.Γ => (0 : ℝ))
        exact (LipschitzWith.const (0 : ℝ)).weaken (show 0 ≤ Lip from zero_le)
    | some c => simpa only [obs', hs, Option.elim_some] using hl w c
  refine ⟨recipe, ⟨obs', g', x', 1, Lip, zero_le_one, hobs, hLip, rfl⟩,
    piecewiseLinearNilsequence_abs_le D.Γ F gap obs' g' x' 1 hobs, ?_⟩
  intro w hw c hc
  obtain ⟨hM, hq, hm, hg⟩ := hgeom w hw
  have hp (t : Fin (q w)) :
      intervalResiduePiece (F.gap w (gap w).val) (F.modulus w : ℕ)
        (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) = label w c := by
    rw [hg, hm]
    exact (mem_intervalResidueSet_iff_piece (M w * q w) (M w) (Nat.mul_pos hM hq)
      c.val.1 c.val.2 _).mp (completeResidueCellPoint_mem _ _ _ hM _ _)
  have he (t : Fin (q w)) :
      recipe w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) =
        obs w c (pieceLinearOrbit D.Γ (M w) (fun _ : Unit => g w c) (fun _ => x w c) ()
          (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t)) := by
    simp only [recipe, piecewiseLinearNilsequence, hp t, obs', g', x',
      hσgood w c ⟨hw, hc⟩, Option.elim_some, pieceLinearOrbit]
    rw [hm]
  simp_rw [he]
  exact hcorr w c ⟨hw, hc⟩

end Hindman168
