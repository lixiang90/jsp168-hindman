import Hindman168.LeibmanCubeCommonCharacter
import Hindman168.LeibmanDenseDirectionReconstruction

namespace Hindman168
open scoped BigOperators Classical

theorem leibman_equal_cube_common_dense_directions {n : ℕ} {C : Type*}
    (N L d : ℕ) (hL : 0 < L) (hN : L^2 ≤ N)
    (f : (Fin n → ℤ) → ℂ) (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ)
    (hsize : 8*(n : ℝ) ≤ δ*L)
    (hf : ∀ x, ‖f x‖ ≤ B)
    (hbad : δ*B ≤ ‖finiteComplexSetMean
      (Fintype.piFinset (fun _ : Fin n => Finset.Ico 0 (N : ℤ))) f‖)
    (A : Finset C) (R : C → (Fin n → ℕ) → (Fin n → ℤ) → Prop)
    (hdir : 8*(d : ℝ)*(A.card : ℝ) < δ*L)
    (hproduce : ∀ q ∈ Fintype.piFinset (fun _ : Fin n => Finset.range L),
      ∀ x ∈ Fintype.piFinset (fun _ : Fin n => Finset.Ico 0 (N : ℤ)),
      δ*B/2 ≤ ‖finiteComplexSetMean (Finset.range (N/L^2))
        (fun m => f (fun j => x j+(q j : ℤ)*(m : ℤ)))‖ → ∃ c ∈ A, R c q x) :
    ∃ c ∈ A, ∃ T : Finset (Fin n → ℕ),
      T ⊆ Fintype.piFinset (fun _ : Fin n => Finset.range L) ∧ d*L^n < T.card*L ∧
      ∀ q ∈ T, δ/(8*(A.card : ℝ))*
        ((Fintype.piFinset (fun _ : Fin n => Finset.Ico 0 (N : ℤ))).card : ℝ) ≤
        (((Fintype.piFinset (fun _ : Fin n => Finset.Ico 0 (N : ℤ))).filter
          (R c q)).card : ℝ) := by
  have hsz : 8*(Fintype.card (Fin n) : ℝ) ≤ δ*L := by
    simpa only [Fintype.card_fin] using hsize
  have hSc : @Fintype.piFinset (Fin n) (Classical.decEq _) (Fin.fintype n)
      (fun _ => ℤ) (fun _ => Finset.Ico 0 (N : ℤ)) =
      Fintype.piFinset (fun _ : Fin n => Finset.Ico 0 (N : ℤ)) := by
    ext x
    simp only [Fintype.mem_piFinset]
  have hTc : @Fintype.piFinset (Fin n) (Classical.decEq _) (Fin.fintype n)
      (fun _ => ℕ) (fun _ => Finset.range L) =
      Fintype.piFinset (fun _ : Fin n => Finset.range L) := by
    ext q
    simp only [Fintype.mem_piFinset]
  have hselected := leibman_equal_cube_common_candidate (κ := Fin n) (C := C)
    N L hL hN f B δ hB hδ hsz hf (by simpa only [hSc] using hbad) A R
      (by simpa only [hSc, hTc] using hproduce)
  obtain ⟨c, hc, hdense⟩ := hselected
  rw [hSc, hTc] at hdense
  let T := (Fintype.piFinset (fun _ : Fin n => Finset.range L)).filter (fun q =>
    δ/(8*(A.card : ℝ))*
      ((Fintype.piFinset (fun _ : Fin n => Finset.Ico 0 (N : ℤ))).card : ℝ) ≤
      (((Fintype.piFinset (fun _ : Fin n => Finset.Ico 0 (N : ℤ))).filter (R c q)).card : ℝ))
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast (Finset.card_pos.mpr ⟨c, hc⟩)
  have hdegree : (d : ℝ) < (δ/(8*(A.card : ℝ)))*(L : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 8*(A.card : ℝ))).mpr
    nlinarith [hdir]
  have hcount : δ/(8*(A.card : ℝ))*(L : ℝ)^n ≤ (T.card : ℝ) := by
    change δ/(8*(A.card : ℝ))*
      ((Fintype.piFinset (fun _ : Fin n => Finset.range L)).card : ℝ) ≤ (T.card : ℝ) at hdense
    simpa only [Fintype.card_piFinset_const, Finset.card_range, Fintype.card_fin,
      Nat.cast_pow] using hdense
  refine ⟨c, hc, T, Finset.filter_subset _ _,
    leibman_direction_density_card_condition d L hL T _ hdegree hcount, ?_⟩
  intro q hq
  exact (Finset.mem_filter.mp hq).2

theorem leibman_equal_cube_common_spanning_directions {n : ℕ} {C : Type*}
    (J : Finset (Fin n → ℕ)) (N L d : ℕ)
    (hJ : ∀ i ∈ J, ∑ j : Fin n, i j ≤ d) (hL : 0 < L) (hN : L^2 ≤ N)
    (f : (Fin n → ℤ) → ℂ) (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ)
    (hsize : 8*(n : ℝ) ≤ δ*L)
    (hf : ∀ x, ‖f x‖ ≤ B)
    (hbad : δ*B ≤ ‖finiteComplexSetMean
      (Fintype.piFinset (fun _ : Fin n => Finset.Ico 0 (N : ℤ))) f‖)
    (A : Finset C) (R : C → (Fin n → ℕ) → (Fin n → ℤ) → Prop)
    (hdir : 8*(d : ℝ)*(A.card : ℝ) < δ*L)
    (hproduce : ∀ q ∈ Fintype.piFinset (fun _ : Fin n => Finset.range L),
      ∀ x ∈ Fintype.piFinset (fun _ : Fin n => Finset.Ico 0 (N : ℤ)),
      δ*B/2 ≤ ‖finiteComplexSetMean (Finset.range (N/L^2))
        (fun m => f (fun j => x j+(q j : ℤ)*(m : ℤ)))‖ → ∃ c ∈ A, R c q x) :
    ∃ c ∈ A, ∃ T : Finset (Fin n → ℕ),
      T ⊆ Fintype.piFinset (fun _ : Fin n => Finset.range L) ∧
      Submodule.span ℚ ((fun q : Fin n → ℕ => leibmanMonomialVector J
        (fun j => (q j : ℚ))) '' (T : Set (Fin n → ℕ))) = ⊤ ∧
      ∀ q ∈ T, δ/(8*(A.card : ℝ))*
        ((Fintype.piFinset (fun _ : Fin n => Finset.Ico 0 (N : ℤ))).card : ℝ) ≤
        (((Fintype.piFinset (fun _ : Fin n => Finset.Ico 0 (N : ℤ))).filter
          (R c q)).card : ℝ) := by
  obtain ⟨c, hc, T, hT, hdense, hrows⟩ := leibman_equal_cube_common_dense_directions
    (n := n) (C := C) N L d hL hN f B δ hB hδ hsize hf hbad A R hdir hproduce
  exact ⟨c, hc, T, hT, leibman_dense_integer_directions_span J d hJ L hL T hT hdense, hrows⟩

end Hindman168
