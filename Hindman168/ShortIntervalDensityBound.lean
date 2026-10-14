import Hindman168.UniformImageHaarDensity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Hindman168

theorem shortInterval_card_ratio (m J : ℕ) (hJ : 0 < J) (hL : 0 < m / J) :
    (m : ℝ) / (m / J : ℕ) ≤ 2 * J := by
  have hr := Nat.mod_lt m hJ
  have he := Nat.mod_add_div m J
  have hb : m ≤ 2 * J * (m / J) := by nlinarith
  have hp : (0 : ℝ) < (m / J : ℕ) := by exact_mod_cast hL
  apply (div_le_iff₀ hp).mpr
  exact_mod_cast hb

theorem shortInterval_uniform_density_le {A : Type*} [Fintype A]
    (J : ℕ) (hJ : 0 < J) (hL : 0 < Fintype.card A / J)
    (e : Fin (Fintype.card A / J) → A) (a : A) :
    uniformImageHaarDensity e a ≤ 2 * J := by
  have hb := uniformImageHaarDensity_le e a
  simp only [Fintype.card_fin] at hb
  exact hb.trans (shortInterval_card_ratio (Fintype.card A) J hJ hL)

theorem shortZModInterval_injective (m L : ℕ) [NeZero m] (hL : L ≤ m) :
    Function.Injective (fun u : Fin L => (u.val : ZMod m)) := by
  intro u v huv
  apply Fin.ext
  have hu : u.val < m := lt_of_lt_of_le u.isLt hL
  have hv : v.val < m := lt_of_lt_of_le v.isLt hL
  simpa only [ZMod.val_natCast_of_lt hu, ZMod.val_natCast_of_lt hv] using congrArg ZMod.val huv

end Hindman168
