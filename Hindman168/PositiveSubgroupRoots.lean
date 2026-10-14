import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Conj

/-! Positive-degree roots of an actual specified subgroup are defined
as a set. Only inverse closure and multiplication of commuting roots
are proved here. General noncommuting multiplication is not assumed. -/

namespace Hindman168
open Set

variable {G : Type*} [Group G]

def positiveSubgroupRoots (Γ : Subgroup G) : Set G :=
  {g | ∃ n : ℕ, 0 < n ∧ g ^ n ∈ Γ}

theorem subgroup_mem_positiveRoots (Γ : Subgroup G) {g : G} (hg : g ∈ Γ) :
    g ∈ positiveSubgroupRoots Γ :=
  ⟨1, Nat.zero_lt_one, by simpa only [pow_one] using hg⟩

theorem positiveSubgroupRoots_inv (Γ : Subgroup G) {g : G}
    (hg : g ∈ positiveSubgroupRoots Γ) : g⁻¹ ∈ positiveSubgroupRoots Γ := by
  obtain ⟨n, hn, hgn⟩ := hg
  exact ⟨n, hn, by simpa only [inv_pow] using Γ.inv_mem hgn⟩

theorem positiveSubgroupRoots_mul_of_commute (Γ : Subgroup G) {g h : G}
    (hg : g ∈ positiveSubgroupRoots Γ) (hh : h ∈ positiveSubgroupRoots Γ)
    (hcomm : Commute g h) : g * h ∈ positiveSubgroupRoots Γ := by
  obtain ⟨n, hn, hgn⟩ := hg
  obtain ⟨m, hm, hhm⟩ := hh
  refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
  rw [hcomm.mul_pow]
  apply Γ.mul_mem
  · rw [pow_mul]
    exact Γ.pow_mem hgn m
  · rw [Nat.mul_comm, pow_mul]
    exact Γ.pow_mem hhm n

theorem positiveSubgroupRoots_root (Γ : Subgroup G) {g : G} {m : ℕ}
    (hm : 0 < m) (hg : g ^ m ∈ positiveSubgroupRoots Γ) :
    g ∈ positiveSubgroupRoots Γ := by
  obtain ⟨n, hn, hgn⟩ := hg
  exact ⟨m * n, Nat.mul_pos hm hn, by simpa only [pow_mul] using hgn⟩

theorem positiveSubgroupRoots_conjugation (Γ : Subgroup G) {a g : G}
    (ha : a ∈ Γ) (hg : g ∈ positiveSubgroupRoots Γ) :
    a * g * a⁻¹ ∈ positiveSubgroupRoots Γ := by
  obtain ⟨n, hn, hgn⟩ := hg
  refine ⟨n, hn, ?_⟩
  rw [conj_pow]
  exact Γ.mul_mem (Γ.mul_mem ha hgn) (Γ.inv_mem ha)

end Hindman168
