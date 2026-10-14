import Hindman168.RoughPartitionScaleThresholds
import Mathlib.Order.Filter.AtTopBot.Field

namespace Hindman168
open Filter Asymptotics
open scoped Topology

theorem rough_residue_scale_power_dominates {α : Type*} {l : Filter α} {S Z : α → ℝ}
    (hg : PowerDominates l Z S) (K : ℝ) (hK : 0 < K) :
    PowerDominates l (fun w => Z w/K) S := by
  intro n
  apply isLittleO_iff.mpr
  intro ε hε
  filter_upwards [(hg n).bound (div_pos hε hK)] with w hw
  simp only [norm_div, Real.norm_eq_abs, abs_of_pos hK]
  simp only [Real.norm_eq_abs] at hw
  convert hw using 1
  ring

theorem rough_residue_scale_eventually_large {α : Type*} {l : Filter α} {S Z : α → ℝ}
    (hg : PowerDominates l Z S) (hS : ∀ᶠ w in l, 1 ≤ S w)
    (hZ : ∀ᶠ w in l, 0 ≤ Z w) (K : ℝ) (hK : 0 < K) :
    ∀ᶠ w in l, 1 < Z w/K := by
  filter_upwards [rough_linear_scale_strict hg hS hZ K hK.le, hS] with w hw hs
  apply (lt_div_iff₀ hK).mpr
  nlinarith

theorem rough_residue_scale_paper_ratios {α : Type*} {l : Filter α} {S Z : α → ℝ}
    (hr : ∀ a : ℝ, 0 < a → Tendsto (fun w => Z w/(S w)^a) l atTop)
    (K : ℝ) (hK : 0 < K) :
    ∀ a : ℝ, 0 < a → Tendsto (fun w => (Z w/K)/(S w)^a) l atTop := by
  intro a ha
  have hh := (tendsto_div_const_atTop_of_pos hK).mpr (hr a ha)
  convert hh using 1
  funext w
  ring

end Hindman168
