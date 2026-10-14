import Hindman168.LeibmanCubeShortLines
import Hindman168.FiniteCandidateDenseRows

namespace Hindman168
open scoped BigOperators Classical

/-- The analytic production of a candidate on each large short line is an
explicit input; the common candidate and both densities are proved here. -/
theorem leibman_equal_cube_common_candidate {κ C : Type*} [Fintype κ]
    (N L : ℕ) (hL : 0 < L) (hN : L^2 ≤ N)
    (f : (κ → ℤ) → ℂ) (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ)
    (hsize : 8*(Fintype.card κ : ℝ) ≤ δ*L)
    (hf : ∀ x, ‖f x‖ ≤ B)
    (hbad : δ*B ≤ ‖finiteComplexSetMean
      (Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ))) f‖)
    (A : Finset C) (R : C → (κ → ℕ) → (κ → ℤ) → Prop)
    (hproduce : ∀ q ∈ Fintype.piFinset (fun _ : κ => Finset.range L),
      ∀ x ∈ Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ)),
      δ*B/2 ≤ ‖finiteComplexSetMean (Finset.range (N/L^2))
        (fun n => f (fun j => x j+(q j : ℤ)*(n : ℤ)))‖ → ∃ c ∈ A, R c q x) :
    ∃ c ∈ A, δ/(8*(A.card : ℝ))*
      ((Fintype.piFinset (fun _ : κ => Finset.range L)).card : ℝ) ≤
      (((Fintype.piFinset (fun _ : κ => Finset.range L)).filter (fun q =>
        δ/(8*(A.card : ℝ))*
          ((Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ))).card : ℝ) ≤
          (((Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ))).filter
            (R c q)).card : ℝ))).card : ℝ) := by
  let T := Fintype.piFinset (fun _ : κ => Finset.range L)
  let S := Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ))
  have hNp : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hT : T.Nonempty := Fintype.piFinset_nonempty.mpr (fun _ => Finset.nonempty_range_iff.mpr hL.ne')
  have hS : S.Nonempty := Fintype.piFinset_nonempty.mpr (fun _ =>
    ⟨0, Finset.mem_Ico.mpr ⟨le_rfl, by exact_mod_cast hNp⟩⟩)
  have hrows : ∀ q ∈ T, δ/4*(S.card : ℝ) ≤
      ((S.filter (fun x => ∃ c ∈ A, R c q x)).card : ℝ) := by
    intro q hq
    have hqL : ∀ j, q j ≤ L := fun j =>
      le_of_lt (Finset.mem_range.mp (Fintype.mem_piFinset.mp hq j))
    have hd := leibman_equal_cube_dense_short_lines N L hL hN q hqL f B δ hB hδ.le hsize hf hbad
    refine hd.trans ?_
    have hsub : (S.filter (fun x => δ*B/2 ≤ ‖finiteComplexSetMean (Finset.range (N/L^2))
        (fun n => f (fun j => x j+(q j : ℤ)*(n : ℤ)))‖)) ⊆
        S.filter (fun x => ∃ c ∈ A, R c q x) := by
      intro x hx
      obtain ⟨hxS, hxlarge⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hxS, hproduce q hq x hxS hxlarge⟩
    exact_mod_cast Finset.card_le_card hsub
  obtain ⟨c, hc, hd⟩ := finite_candidate_dense_rows T S A hT hS (δ/4) (by positivity) R hrows
  have heq : (δ/4)/(2*(A.card : ℝ)) = δ/(8*(A.card : ℝ)) := by ring
  refine ⟨c, hc, ?_⟩
  simpa only [heq, T, S] using hd

end Hindman168
