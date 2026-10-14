import Mathlib.Algebra.Lie.Nilpotent

/-! Brackets between the actual lower central layers. Mathlib numbers the
whole algebra as layer zero, so the bracket index is j+k+1. -/

namespace Hindman168

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

theorem alignmentLie_lowerCentral_bracket {j k : ℕ} {x y : L}
    (hx : x ∈ LieModule.lowerCentralSeries R L L j)
    (hy : y ∈ LieModule.lowerCentralSeries R L L k) :
    ⁅x, y⁆ ∈ LieModule.lowerCentralSeries R L L (j + k + 1) := by
  induction j generalizing k x y with
  | zero =>
      simpa only [Nat.zero_add, LieModule.lowerCentralSeries_succ] using
        LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) hy
  | succ j ih =>
      rw [LieModule.lowerCentralSeries_succ] at hx
      change x ∈ (⁅(⊤ : LieIdeal R L),
        LieModule.lowerCentralSeries R L L j⁆).toSubmodule at hx
      rw [LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
      induction hx using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨a, _, b, hb, rfl⟩ := hz
          rw [lie_lie]
          apply (LieModule.lowerCentralSeries R L L (j + 1 + k + 1)).sub_mem
          · have h := LieSubmodule.lie_mem_lie (LieSubmodule.mem_top a) (ih hb hy)
            simpa only [← LieModule.lowerCentralSeries_succ, Nat.succ_add,
              LieSubmodule.mem_toSubmodule] using h
          · have h := LieSubmodule.lie_mem_lie (LieSubmodule.mem_top a) hy
            rw [← LieModule.lowerCentralSeries_succ] at h
            simpa only [Nat.succ_add, Nat.add_succ,
              LieSubmodule.mem_toSubmodule] using ih hb h
      | zero => simpa only [zero_lie] using
          (LieModule.lowerCentralSeries R L L (j + 1 + k + 1)).zero_mem
      | add a b _ _ ha hb =>
          rw [add_lie]
          exact (LieModule.lowerCentralSeries R L L (j + 1 + k + 1)).add_mem ha hb
      | smul r a _ ha =>
          rw [smul_lie]
          exact (LieModule.lowerCentralSeries R L L (j + 1 + k + 1)).smul_mem r ha

theorem alignmentLie_weighted_lowerCentral_bracket {d e : ℕ} {x y : L}
    (hx : x ∈ LieModule.lowerCentralSeries R L L (d - 1))
    (hy : y ∈ LieModule.lowerCentralSeries R L L (e - 1)) :
    ⁅x, y⁆ ∈ LieModule.lowerCentralSeries R L L (d + e - 1) := by
  exact LieModule.antitone_lowerCentralSeries R L L (by omega)
    (alignmentLie_lowerCentral_bracket hx hy)

end Hindman168
