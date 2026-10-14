import Hindman168.CubeLocalBoxGeometry
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-! The paper's independent base/increment windows and their eventual nonemptiness. -/
namespace Hindman168
open Filter
open scoped Topology

def cubeAlphaLower (d : ℕ) (beta L : ℝ) : Fin (d+1) → ℝ :=
  Fin.cases (beta*L) (fun _ => 0)

def cubeAlphaUpper (d : ℕ) (beta L α : ℝ) : Fin (d+1) → ℝ :=
  fun j => cubeAlphaLower d beta L j + α*L

def cubeAlphaResidue (d : ℕ) (b : ℤ) : Fin (d+1) → ℤ :=
  Fin.cases b (fun _ => 0)

theorem cube_standard_alpha_geometry (d : ℕ) (beta L α : ℝ) (h : 0 ≤ α*L) :
    (∀ j, cubeAlphaUpper d beta L α j-cubeAlphaLower d beta L j = α*L) ∧
    (|cubeAlphaLower d beta L 0-beta*L| ≤ α*L ∧ |cubeAlphaUpper d beta L α 0-beta*L| ≤ α*L) ∧
    (∀ i : Fin d, |cubeAlphaLower d beta L i.succ| ≤ α*L ∧ |cubeAlphaUpper d beta L α i.succ| ≤ α*L) := by
  simp only [cubeAlphaUpper,cubeAlphaLower,Fin.cases_zero,Fin.cases_succ,add_sub_cancel_left,
    sub_self,abs_zero,zero_add,abs_of_nonneg h]
  exact ⟨fun _ => trivial,⟨h,le_rfl⟩,fun _ => ⟨h,le_rfl⟩⟩

theorem cube_standard_alpha_box_nonempty {d : ℕ} (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (beta α : ℝ) (hα : 0 < α) (t : ℕ) (ht : 0 < t) (b : ℤ) :
    ∀ᶠ m in atTop, (alignmentBoxClass
      (fun j => ⌈cubeAlphaLower d beta (L m) j⌉)
      (fun j => ⌈cubeAlphaUpper d beta (L m) α j⌉) (cubeAlphaResidue d b) t).Nonempty := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  filter_upwards [hL.eventually_ge_atTop 1,hL.eventually_ge_atTop (4*(t : ℝ)/α)] with m hm hlarge
  have hbig : 4*(t : ℝ) ≤ α*L m := by
    simpa only [mul_comm] using (div_le_iff₀ hα).mp hlarge
  apply alignmentBoxClass_nonempty _ _ _ t ht
  intro j
  have hside := cube_local_ceil_side_bounds (cubeAlphaLower d beta (L m) j)
    (cubeAlphaUpper d beta (L m) α j) (L m) α α hm (by linarith)
    (by simp only [cubeAlphaUpper,add_sub_cancel_left]; exact ⟨le_rfl,le_rfl⟩)
  have hlen : 2*(t : ℝ) ≤ (⌈cubeAlphaUpper d beta (L m) α j⌉ : ℝ) -
      (⌈cubeAlphaLower d beta (L m) j⌉ : ℝ) := by linarith [hside.1]
  exact_mod_cast hlen


theorem cube_standard_alpha_box_mem {d : ℕ} (beta L α : ℝ) (hL : 0 < L)
    (t b : ℤ) (x : Fin (d+1) → ℤ) :
    x ∈ alignmentBoxClass (fun j => ⌈cubeAlphaLower d beta L j⌉)
      (fun j => ⌈cubeAlphaUpper d beta L α j⌉) (cubeAlphaResidue d b) t ↔
      ((beta ≤ (x 0 : ℝ)/L ∧ (x 0 : ℝ)/L < beta+α) ∧ Int.ModEq t b (x 0)) ∧
      ∀ i : Fin d, ((0 ≤ (x i.succ : ℝ)/L ∧ (x i.succ : ℝ)/L < α) ∧ Int.ModEq t 0 (x i.succ)) := by
  rw [alignment_ceil_box_mem,Fin.forall_fin_succ]
  simp only [cubeAlphaLower,cubeAlphaUpper,cubeAlphaResidue,Fin.cases_zero,Fin.cases_succ,
    le_div_iff₀ hL,div_lt_iff₀ hL,zero_mul,zero_add,add_mul]

end Hindman168
