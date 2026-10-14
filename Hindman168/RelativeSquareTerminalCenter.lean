import Hindman168.RelativeSquareFiltration
import Mathlib.Algebra.Group.Center

/-! The TERMINAL diagonal layer is central. The entire original center
need not equal that layer, and is not substituted for it. -/

namespace Hindman168
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem relative_terminal_diagonal_le_center (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (h1 : F 1 = ⊤) (d : ℕ) (hd : F (d+1) = ⊥) :
    relativeDiagonalSubgroup (F d) ≤ Subgroup.center (G × G) := by
  intro p hp
  obtain ⟨hp1,he⟩ := (relative_diagonal_mem_iff (F d) p).mp hp
  have hc : p.1 ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    have hg : g ∈ F 1 := h1 ▸ Subgroup.mem_top g
    have hb := hF.commutator_mem 1 d g hg p.1 hp1
    rw [Nat.add_comm 1 d,hd,Subgroup.mem_bot] at hb
    exact commutatorElement_eq_one_iff_mul_comm.mp hb
  apply Subgroup.mem_center_iff.mpr
  intro q
  apply Prod.ext
  · exact Subgroup.mem_center_iff.mp hc q.1
  · change q.2 * p.2 = p.2 * q.2
    rw [← he]
    exact Subgroup.mem_center_iff.mp hc q.2

theorem relative_terminal_diagonal_normal (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (h1 : F 1 = ⊤) (d : ℕ) (hd : F (d+1) = ⊥) :
    (relativeDiagonalSubgroup (F d)).Normal := by
  refine ⟨?_⟩
  intro p hp q
  have hc := relative_terminal_diagonal_le_center F hF h1 d hd hp
  simpa only [Subgroup.mem_center_iff.mp hc q,mul_inv_cancel_right] using hp

end Hindman168
