import Hindman168.RoughDescentSystem

namespace Hindman168
open Polynomial Filter
open scoped Topology

theorem rough_simultaneous_descent_partial
    {α ι : Type*} {l : Filter α} {W : α → ℕ} (hW : Tendsto W l atTop)
    {S Z : α → ℝ} (hg : PowerDominates l Z S)
    (hS : ∀ᶠ w in l, 1 ≤ S w) (hZ : ∀ᶠ w in l, 0 < Z w)
    (s : Finset ι) (e : ι → ℕ) (q H : ℕ) (hH : 2 * q + 2 ≤ H)
    (he : ∀ i ∈ s, 0 < e i ∧ e i ≤ q)
    (A0 B : ℝ) (hA : 0 < A0) (hB : 0 ≤ B)
    (k : ℕ) (hk : k ≤ q) :
    ∀ᶠ w in l, ∀ (t m : ℕ) (theta : ι → ℝ[X])
      (p : ι → ℕ → ℕ) (c : ι → ℕ → ι → ℤ),
      RoughHorizontalSystem s e (W w) H q t m (S w) (Z w) A0 B theta p c →
      ∃ M : ι → ℚ[X], ∀ i ∈ s, q - k < e i →
        RoughCoefficientModel (W w) H q (e i) (Z w)
          (roughDescentConstant q s.card A0 B k) (theta i) (M i) := by
  classical
  induction k with
  | zero =>
    apply Filter.Eventually.of_forall
    intro w t m theta p c _
    refine ⟨fun _ => 0, ?_⟩
    intro i hi hlt
    have hbound := (he i hi).2
    omega
  | succ k ih =>
    have hprev := ih (by omega)
    have hsteps := (s.eventually_all).mpr (fun i hi =>
      rough_descent_system_step hW hg hS hZ s e q H k hH A0 B hA hB i hi
        (he i hi).1 (he i hi).2)
    filter_upwards [hprev, hsteps, hZ] with w hw hs hz
    intro t m theta p c hsys
    obtain ⟨Mold, hOld⟩ := hw t m theta p c hsys
    have hex : ∀ i, ∃ Mi : ℚ[X], i ∈ s → q - (k + 1) < e i →
        RoughCoefficientModel (W w) H q (e i) (Z w)
          (roughDescentConstant q s.card A0 B (k + 1)) (theta i) Mi := by
      intro i
      by_cases hi : i ∈ s
      · by_cases hnew : q - (k + 1) < e i
        · by_cases hold : q - k < e i
          · refine ⟨Mold i, fun _ _ => ?_⟩
            exact rough_coefficient_model_mono (hOld i hi hold) hz.le
              (roughDescentConstant_le_succ q s.card hA hB k)
          · have hei : e i = q - k := by omega
            obtain ⟨Mi, hMi⟩ := hs i hi t m theta p c Mold hsys (by
              intro j hj hij
              apply hOld j hj
              omega)
            exact ⟨Mi, fun _ _ => hMi⟩
        · exact ⟨0, fun _ hlt => (hnew hlt).elim⟩
      · exact ⟨0, fun hmem _ => (hi hmem).elim⟩
    choose M hM using hex
    exact ⟨M, fun i hi hl => hM i hi hl⟩

theorem rough_simultaneous_descent
    {α ι : Type*} {l : Filter α} {W : α → ℕ} (hW : Tendsto W l atTop)
    {S Z : α → ℝ} (hg : PowerDominates l Z S)
    (hS : ∀ᶠ w in l, 1 ≤ S w) (hZ : ∀ᶠ w in l, 0 < Z w)
    (s : Finset ι) (e : ι → ℕ) (q H : ℕ) (hH : 2 * q + 2 ≤ H)
    (he : ∀ i ∈ s, 0 < e i ∧ e i ≤ q)
    (A0 B : ℝ) (hA : 0 < A0) (hB : 0 ≤ B) :
    ∀ᶠ w in l, ∀ (t m : ℕ) (theta : ι → ℝ[X])
      (p : ι → ℕ → ℕ) (c : ι → ℕ → ι → ℤ),
      RoughHorizontalSystem s e (W w) H q t m (S w) (Z w) A0 B theta p c →
      ∃ M : ι → ℚ[X], ∀ i ∈ s,
        RoughCoefficientModel (W w) H q (e i) (Z w)
          (roughDescentConstant q s.card A0 B q) (theta i) (M i) := by
  filter_upwards [rough_simultaneous_descent_partial hW hg hS hZ s e q H hH he A0 B hA hB q le_rfl] with w hw
  intro t m theta p c hsys
  obtain ⟨M, hM⟩ := hw t m theta p c hsys
  exact ⟨M, fun i hi => hM i hi (by simpa only [Nat.sub_self] using (he i hi).1)⟩

end Hindman168
