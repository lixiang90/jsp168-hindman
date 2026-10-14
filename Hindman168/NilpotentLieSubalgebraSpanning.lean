import Mathlib.Algebra.Lie.Nilpotent

/-! A Lie subalgebra generating the abelianization of a nilpotent Lie
algebra generates the whole algebra. The proof explicitly descends through
the actual lower central series using bracket bilinearity. -/

namespace Hindman168
open Set Submodule

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

 theorem lieSubalgebra_sup_commutator_le_next
    (S : LieSubalgebra R L) (j : ℕ)
    (h : S.toSubmodule ⊔ (LieModule.lowerCentralSeries R L L j).toSubmodule = ⊤) :
    S.toSubmodule ⊔ (LieModule.lowerCentralSeries R L L 1).toSubmodule ≤
      S.toSubmodule ⊔ (LieModule.lowerCentralSeries R L L (j + 1)).toSubmodule := by
  apply sup_le le_sup_left
  rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span']
  apply span_le.mpr
  rintro z ⟨x, _, y, _, rfl⟩
  have hx : x ∈ S.toSubmodule ⊔ (LieModule.lowerCentralSeries R L L j).toSubmodule := by
    rw [h]
    trivial
  have hy : y ∈ S.toSubmodule ⊔ (LieModule.lowerCentralSeries R L L j).toSubmodule := by
    rw [h]
    trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := mem_sup.mp hy
  have hright : ∀ u : L, ∀ v ∈ LieModule.lowerCentralSeries R L L j,
      ⁅u, v⁆ ∈ LieModule.lowerCentralSeries R L L (j + 1) := by
    intro u v hv
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top u) hv
  have hleft : ⁅b, c⁆ ∈ LieModule.lowerCentralSeries R L L (j + 1) := by
    rw [← lie_skew b c]
    exact (LieModule.lowerCentralSeries R L L (j + 1)).toSubmodule.neg_mem (hright c b hb)
  rw [add_lie, lie_add, lie_add]
  apply Submodule.add_mem
  · exact Submodule.add_mem _ (mem_sup_left (S.lie_mem ha hc)) (mem_sup_right (hright a d hd))
  · exact mem_sup_right ((LieModule.lowerCentralSeries R L L (j + 1)).toSubmodule.add_mem
      hleft (hright b d hd))

 theorem nilpotentLieSubalgebra_eq_top_of_sup_commutator_eq_top
    (S : LieSubalgebra R L)
    (hnil : ∃ k, LieModule.lowerCentralSeries R L L k = ⊥)
    (h : S.toSubmodule ⊔ (LieModule.lowerCentralSeries R L L 1).toSubmodule = ⊤) :
    S = ⊤ := by
  have hall : ∀ j : ℕ,
      S.toSubmodule ⊔ (LieModule.lowerCentralSeries R L L (j + 1)).toSubmodule = ⊤ := by
    intro j
    induction j with
    | zero => exact h
    | succ j ih =>
      apply top_le_iff.mp
      rw [← h]
      exact lieSubalgebra_sup_commutator_le_next S (j + 1) ih
  obtain ⟨k, hk⟩ := hnil
  have hk' : LieModule.lowerCentralSeries R L L (k + 1) = ⊥ := by
    apply eq_bot_iff.mpr
    rw [← hk]
    exact LieModule.antitone_lowerCentralSeries R L L (Nat.le_succ k)
  have hs := hall k
  rw [hk'] at hs
  have hs' : S.toSubmodule = ⊤ := by simpa using hs
  apply SetLike.ext
  intro x
  change x ∈ S.toSubmodule ↔ x ∈ (⊤ : Submodule R L)
  rw [hs']

 theorem nilpotentLieSubalgebra_sup_commutator_ne_top
    (S : LieSubalgebra R L)
    (hnil : ∃ k, LieModule.lowerCentralSeries R L L k = ⊥) (hS : S ≠ ⊤) :
    S.toSubmodule ⊔ (LieModule.lowerCentralSeries R L L 1).toSubmodule ≠ ⊤ :=
  fun h => hS (nilpotentLieSubalgebra_eq_top_of_sup_commutator_eq_top S hnil h)

end Hindman168
