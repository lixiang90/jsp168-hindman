import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Nilpotent

/-! Algebraic subgroup generation and commutators preserve sigma compactness.
This concerns algebraic closure, not topological closure. -/

namespace Hindman168
open Set
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Group G] [IsTopologicalGroup G] in
theorem sigmaCompact_set_union {s t : Set G} (hs : IsSigmaCompact s) (ht : IsSigmaCompact t) :
    IsSigmaCompact (s ∪ t) := by
  obtain ⟨K, hK, rfl⟩ := hs
  obtain ⟨L, hL, rfl⟩ := ht
  refine ⟨fun n => K n ∪ L n, fun n => (hK n).union (hL n), ?_⟩
  exact iUnion_union_distrib K L

theorem sigmaCompact_set_mul {s t : Set G} (hs : IsSigmaCompact s) (ht : IsSigmaCompact t) :
    IsSigmaCompact (s * t) := by
  obtain ⟨K, hK, hKs⟩ := hs
  obtain ⟨L, hL, hLt⟩ := ht
  have he : s * t = ⋃ p : ℕ × ℕ, K p.1 * L p.2 := by
    rw [← hKs, ← hLt]
    ext g
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      obtain ⟨m, hm⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨(n, m), x, hn, y, hm, rfl⟩
    · intro hg
      obtain ⟨⟨n, m⟩, x, hx, y, hy, rfl⟩ := mem_iUnion.mp hg
      exact ⟨x, mem_iUnion.mpr ⟨n, hx⟩, y, mem_iUnion.mpr ⟨m, hy⟩, rfl⟩
  rw [he]
  exact isSigmaCompact_iUnion_of_isCompact _ (fun p => (hK p.1).mul (hL p.2))

theorem sigmaCompact_algebraic_subgroup_closure {s : Set G} (hs : IsSigmaCompact s) :
    IsSigmaCompact (Subgroup.closure s : Set G) := by
  let A : Set G := s ∪ s⁻¹
  have hi : IsSigmaCompact s⁻¹ := by
    simpa using IsSigmaCompact.image continuous_inv hs
  have hA : IsSigmaCompact A := sigmaCompact_set_union hs hi
  have hp : ∀ n : ℕ, IsSigmaCompact (A ^ n) := by
    intro n
    induction n with
    | zero =>
      change IsSigmaCompact ({1} : Set G)
      exact isCompact_singleton.isSigmaCompact
    | succ n ih => rw [pow_succ']; exact sigmaCompact_set_mul hA ih
  have he : (Subgroup.closure s : Set G) = ⋃ n : ℕ, A ^ n := by
    ext g
    constructor
    · intro hg
      apply mem_iUnion.mpr
      induction hg using Subgroup.closure_induction_left with
      | one => exact ⟨0, by simp⟩
      | mul_left x hx y _ ih =>
        obtain ⟨n, hn⟩ := ih
        refine ⟨n + 1, ?_⟩
        rw [pow_succ']
        exact ⟨x, Or.inl hx, y, hn, rfl⟩
      | inv_mul_cancel x hx y _ ih =>
        obtain ⟨n, hn⟩ := ih
        refine ⟨n + 1, ?_⟩
        rw [pow_succ']
        exact ⟨x⁻¹, Or.inr (by simpa using hx), y, hn, rfl⟩
    · intro hg
      obtain ⟨n, hn⟩ := mem_iUnion.mp hg
      have hsub : A ⊆ (Subgroup.closure s : Set G) := by
        intro x hx
        rcases hx with hx | hx
        · exact Subgroup.subset_closure hx
        · change x ∈ Subgroup.closure s
          simpa only [inv_inv] using (Subgroup.closure s).inv_mem (Subgroup.subset_closure hx)
      have hall : ∀ n : ℕ, A ^ n ⊆ (Subgroup.closure s : Set G) := by
        intro n
        induction n with
        | zero =>
          intro x hx
          have hx1 : x = 1 := by simpa using hx
          subst x
          exact (Subgroup.closure s).one_mem
        | succ n ih =>
          rw [pow_succ']
          rintro x ⟨a, ha, b, hb, rfl⟩
          exact (Subgroup.closure s).mul_mem (hsub ha) (ih hb)
      exact hall n hn
  rw [he]
  exact isSigmaCompact_iUnion _ hp

theorem sigmaCompact_subgroup_commutator (H K : Subgroup G)
    (hH : IsSigmaCompact (H : Set G)) (hK : IsSigmaCompact (K : Set G)) :
    IsSigmaCompact ((⁅H, K⁆ : Subgroup G) : Set G) := by
  letI : SigmaCompactSpace H := isSigmaCompact_iff_sigmaCompactSpace.mp hH
  letI : SigmaCompactSpace K := isSigmaCompact_iff_sigmaCompactSpace.mp hK
  let f : H × K → G := fun p => ⁅p.1.val, p.2.val⁆
  have hf : Continuous f := by
    dsimp only [f]
    simp only [commutatorElement_def]
    fun_prop
  have he : {g : G | ∃ h ∈ H, ∃ k ∈ K, ⁅h, k⁆ = g} = range f := by
    ext g
    constructor
    · rintro ⟨h, hh, k, hk, rfl⟩
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), rfl⟩
    · rintro ⟨⟨h, k⟩, rfl⟩
      exact ⟨h.val, h.property, k.val, k.property, rfl⟩
  rw [Subgroup.commutator_def, he]
  exact sigmaCompact_algebraic_subgroup_closure (isSigmaCompact_range hf)

theorem sigmaCompact_subgroup_lowerCentralSeries (H : Subgroup G)
    (hH : IsSigmaCompact (H : Set G)) (j : ℕ) :
    IsSigmaCompact (H.lowerCentralSeries j : Set G) := by
  induction j with
  | zero => simpa only [Subgroup.lowerCentralSeries_zero] using hH
  | succ j ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    exact sigmaCompact_subgroup_commutator _ _ ih hH

end Hindman168
