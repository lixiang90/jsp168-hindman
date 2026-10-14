import Hindman168.RoughCofinalSubsequences
import Mathlib.Data.Nat.Find

/-! Extend actual data on a strictly increasing sieve-width sequence to ALL
natural widths. Only the scale data are extended; no fictitious source/sample
is supplied at unobserved widths. Values at every actual width are EXACT. -/
namespace Hindman168
open Filter

def roughCofinalIndexFloor (width : ℕ → ℕ) (w : ℕ) : ℕ :=
  Nat.findGreatest (fun n => width n ≤ w) w

def roughCofinalExtension {α : Type*} (width : ℕ → ℕ) (f : ℕ → α) : ℕ → α :=
  fun w => f (roughCofinalIndexFloor width w)

theorem rough_strict_nat_sequence_index_le (width : ℕ → ℕ) (hwidth : StrictMono width) :
    ∀ n, n ≤ width n := by
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hs : width n < width (n+1) := hwidth (Nat.lt_succ_self n)
    change n+1 ≤ width (n+1)
    exact (Nat.succ_le_succ ih).trans (Nat.succ_le_of_lt hs)

theorem rough_cofinal_index_floor_at_sample (width : ℕ → ℕ) (hwidth : StrictMono width) (n : ℕ) :
    roughCofinalIndexFloor width (width n)=n := by
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨rough_strict_nat_sequence_index_le width hwidth n,fun _ => le_rfl,?_⟩
  intro m hnm _hmb hwm
  exact (not_le_of_gt (hwidth hnm)) hwm

theorem rough_cofinal_index_floor_tendsto (width : ℕ → ℕ) (hwidth : StrictMono width) :
    Tendsto (roughCofinalIndexFloor width) atTop atTop := by
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [eventually_ge_atTop (width n)] with w hw
  exact Nat.le_findGreatest ((rough_strict_nat_sequence_index_le width hwidth n).trans hw) hw

theorem rough_cofinal_extension_at_sample {α : Type*} (width : ℕ → ℕ)
    (hwidth : StrictMono width) (f : ℕ → α) (n : ℕ) :
    roughCofinalExtension width f (width n)=f n := by
  rw [roughCofinalExtension,rough_cofinal_index_floor_at_sample width hwidth n]

theorem rough_cofinal_extension_tendsto {α : Type*} {l : Filter α}
    (width : ℕ → ℕ) (hwidth : StrictMono width) (f : ℕ → α) (hf : Tendsto f atTop l) :
    Tendsto (roughCofinalExtension width f) atTop l :=
  hf.comp (rough_cofinal_index_floor_tendsto width hwidth)

theorem rough_cofinal_extension_paper_growth (width : ℕ → ℕ) (hwidth : StrictMono width)
    (Scale Z : ℕ → ℝ)
    (hg : ∀ e : ℝ, 0 < e → Tendsto (fun n => Z n/(Scale n)^e) atTop atTop) :
    ∀ e : ℝ, 0 < e → Tendsto (fun w => roughCofinalExtension width Z w/
      (roughCofinalExtension width Scale w)^e) atTop atTop := by
  intro e he
  exact (hg e he).comp (rough_cofinal_index_floor_tendsto width hwidth)

end Hindman168
