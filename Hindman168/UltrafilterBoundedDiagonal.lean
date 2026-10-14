import Hindman168.UltrafilterHilbertEmbedding
import Hindman168.SlowStageDiagonal
import Mathlib.Order.Filter.Finite
import Mathlib.Algebra.Order.Archimedean.Basic

namespace Hindman168
open Filter
open scoped Classical Topology

theorem exists_slow_stage_filter (L : Filter ℕ) (hL : L ≤ atTop) (R : ℕ → ℕ → Prop)
    (hR : ∀ n, ∀ᶠ w in L, R n w) :
    ∃ stage : ℕ → ℕ, Tendsto stage L atTop ∧ (∀ w, stage w ≤ w) ∧
      ∀ᶠ w in L, R (stage w) w := by
  let good (w : ℕ) := (Finset.range (w + 1)).filter (fun n => R n w)
  let stage (w : ℕ) := if hn : (good w).Nonempty then (good w).max' hn else 0
  have hmem {n w : ℕ} (hn : n ≤ w) (hr : R n w) : n ∈ good w :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hr⟩
  refine ⟨stage, ?_, ?_, ?_⟩
  · apply tendsto_atTop.mpr
    intro n
    filter_upwards [(eventually_ge_atTop n).filter_mono hL, hR n] with w hn hr
    have hm := hmem hn hr
    have hne : (good w).Nonempty := ⟨n, hm⟩
    dsimp only [stage]
    rw [dif_pos hne]
    exact (good w).le_max' n hm
  · intro w
    dsimp only [stage]
    split_ifs with hn
    · exact Nat.le_of_lt_succ (Finset.mem_range.mp
        (Finset.mem_filter.mp ((good w).max'_mem hn)).1)
    · exact Nat.zero_le _
  · filter_upwards [hR 0] with w hw
    have hn : (good w).Nonempty := ⟨0, hmem (Nat.zero_le _) hw⟩
    dsimp only [stage]
    rw [dif_pos hn]
    exact (Finset.mem_filter.mp ((good w).max'_mem hn)).2

/-- A uniformly bounded sequence of representatives converging in the completed
ultrafilter Hilbert space has a diagonal representative preserving every coordinate constraint. -/
theorem ultrafilterHilbert_bounded_diagonal
    (E : ℕ → Type*) [∀ w, SeminormedAddCommGroup (E w)] [∀ w, InnerProductSpace ℝ (E w)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (C : ∀ w, E w → Prop)
    (z : UltrafilterHilbertSpace E U) (f : ℕ → boundedHilbertFamilies E)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ n w, ‖(f n).val w‖ ≤ B)
    (hc : ∀ n w, C w ((f n).val w))
    (hf : ∀ n, ‖z - hilbertFamilyToCompletion E U (f n)‖ < 1 / ((n : ℝ) + 1)) :
    ∃ g : boundedHilbertFamilies E, (∀ w, ‖g.val w‖ ≤ B) ∧
      (∀ w, C w (g.val w)) ∧ hilbertFamilyToCompletion E U g = z := by
  let r := fun n : ℕ => 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  let R := fun n w => ∀ k ∈ Finset.range (n + 1), ‖(f n).val w - (f k).val w‖ ^ 2 < (3 * r k) ^ 2
  have hR (n : ℕ) : ∀ᶠ w in (U : Filter ℕ), R n w := by
    change ∀ᶠ w in (U : Filter ℕ), ∀ k ∈ Finset.range (n + 1), _
    apply (eventually_all_finite (Finset.finite_toSet (Finset.range (n + 1)))).mpr
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hmono : r n ≤ r k := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.succ_le_succ hkn
    have hn : ‖hilbertFamilyToCompletion E U (f n) - hilbertFamilyToCompletion E U (f k)‖ < 3 * r k := by
      have ht := norm_sub_le_norm_sub_add_norm_sub (hilbertFamilyToCompletion E U (f n)) z
        (hilbertFamilyToCompletion E U (f k))
      rw [norm_sub_rev (hilbertFamilyToCompletion E U (f n)) z] at ht
      linarith [hf n, hf k, hr k]
    exact (hilbertFamilyToCompletion_norm_sub_sq_tendsto E U (f n) (f k)).eventually
      (eventually_lt_nhds ((sq_lt_sq₀ (norm_nonneg _) (by positivity)).mpr hn))
  obtain ⟨stage, htend, _, hstage⟩ := exists_slow_stage_filter (U : Filter ℕ) hU R hR
  let g : boundedHilbertFamilies E := ⟨fun w => (f (stage w)).val w, B, hB, fun w => hb (stage w) w⟩
  have hnear (k : ℕ) : ‖hilbertFamilyToCompletion E U g - hilbertFamilyToCompletion E U (f k)‖ ≤ 3 * r k := by
    have he : ∀ᶠ w in (U : Filter ℕ), ‖g.val w - (f k).val w‖ ^ 2 ≤ (3 * r k) ^ 2 := by
      filter_upwards [hstage, htend.eventually (eventually_ge_atTop k)] with w hw hk
      exact (hw k (Finset.mem_range.mpr (by omega))).le
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      (le_of_tendsto (hilbertFamilyToCompletion_norm_sub_sq_tendsto E U g (f k)) he)
  have hclose (k : ℕ) : ‖z - hilbertFamilyToCompletion E U g‖ < 4 * r k := by
    have ht := norm_sub_le_norm_sub_add_norm_sub z (hilbertFamilyToCompletion E U (f k))
      (hilbertFamilyToCompletion E U g)
    rw [norm_sub_rev (hilbertFamilyToCompletion E U (f k)) (hilbertFamilyToCompletion E U g)] at ht
    linarith [hf k, hnear k]
  have hz : ‖z - hilbertFamilyToCompletion E U g‖ = 0 := by
    by_contra hn
    have hp : 0 < ‖z - hilbertFamilyToCompletion E U g‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ‖z - hilbertFamilyToCompletion E U g‖ / 4 by positivity)
    have h := hclose k
    dsimp only [r] at h
    linarith
  exact ⟨g, fun w => hb (stage w) w, fun w => hc (stage w) w,
    (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm⟩

end Hindman168
