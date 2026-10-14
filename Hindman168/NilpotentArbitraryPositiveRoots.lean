import Hindman168.NilpotentPowerGenerators

/-! Positive roots of any specified subgroup of any nilpotent group
form a genuine subgroup. Noncommuting multiplication is proved through
the actual two-generator subgroup and the terminating original series.
No normality of the specified subgroup is assumed. -/

namespace Hindman168
open Set Subgroup

variable {G : Type*} [Group G] [Group.IsNilpotent G]

theorem positiveSubgroupRoots_mul_nilpotent (Γ : Subgroup G) {a b : G}
    (ha : a ∈ positiveSubgroupRoots Γ) (hb : b ∈ positiveSubgroupRoots Γ) :
    a * b ∈ positiveSubgroupRoots Γ := by
  obtain ⟨m, hm, ham⟩ := ha
  obtain ⟨n, hn, hbn⟩ := hb
  let K := Subgroup.closure ({a, b} : Set G)
  let R : Set K := K.subtype ⁻¹' ({a, b} : Set G)
  have hR : R.Finite := Set.Finite.preimage Subtype.val_injective.injOn (Set.toFinite _)
  have hgen : Subgroup.closure R = ⊤ := Subgroup.closure_closure_coe_preimage
  have hp : ∀ k ∈ R, k ^ (m * n) ∈ Γ.subgroupOf K := by
    intro k hk
    rcases (show (k : G) = a ∨ (k : G) = b from hk) with he | he
    · change (k : G) ^ (m * n) ∈ Γ
      rw [he, pow_mul]
      exact Γ.pow_mem ham n
    · change (k : G) ^ (m * n) ∈ Γ
      rw [he, Nat.mul_comm m n, pow_mul]
      exact Γ.pow_mem hbn m
  obtain ⟨e, he, hall⟩ := nilpotent_power_generators_uniform (Γ.subgroupOf K)
    R hR hgen (m * n) (Nat.mul_pos hm hn) hp
  have hab : a * b ∈ K := K.mul_mem
    (Subgroup.subset_closure (Set.mem_insert a {b}))
    (Subgroup.subset_closure (Set.mem_insert_of_mem a (Set.mem_singleton b)))
  exact ⟨e, he, hall (⟨a * b, hab⟩ : K)⟩

def nilpotentArbitraryPositiveRootSubgroup (Γ : Subgroup G) : Subgroup G where
  carrier := positiveSubgroupRoots Γ
  one_mem' := subgroup_mem_positiveRoots Γ Γ.one_mem
  mul_mem' := positiveSubgroupRoots_mul_nilpotent Γ
  inv_mem' := positiveSubgroupRoots_inv Γ

theorem nilpotentArbitraryPositiveRootSubgroup_mem_iff (Γ : Subgroup G) (g : G) :
    g ∈ nilpotentArbitraryPositiveRootSubgroup Γ ↔ g ∈ positiveSubgroupRoots Γ := Iff.rfl

theorem nilpotentArbitraryPositiveRootSubgroup_contains (Γ : Subgroup G) :
    Γ ≤ nilpotentArbitraryPositiveRootSubgroup Γ := fun _ hg => subgroup_mem_positiveRoots Γ hg

theorem nilpotentArbitraryPositiveRootSubgroup_root (Γ : Subgroup G) {g : G} {n : ℕ}
    (hn : 0 < n) (hg : g ^ n ∈ nilpotentArbitraryPositiveRootSubgroup Γ) :
    g ∈ nilpotentArbitraryPositiveRootSubgroup Γ :=
  positiveSubgroupRoots_root Γ hn hg

omit [Group.IsNilpotent G] in
theorem finite_positiveRoots_common_power (Γ : Subgroup G) (s : Set G) (hsf : s.Finite)
    (hs : ∀ g ∈ s, g ∈ positiveSubgroupRoots Γ) :
    ∃ N : ℕ, 0 < N ∧ ∀ g ∈ s, g ^ N ∈ Γ := by
  revert hs
  induction s, hsf using Set.Finite.induction_on with
  | empty =>
    intro _
    exact ⟨1, Nat.zero_lt_one, by simp⟩
  | @insert g s _ _ ih =>
    intro hs
    obtain ⟨m, hm, hgm⟩ := hs g (Set.mem_insert g s)
    obtain ⟨n, hn, hsn⟩ := ih (fun a ha => hs a (Set.mem_insert_of_mem g ha))
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · rw [pow_mul]
      exact Γ.pow_mem hgm n
    · rw [Nat.mul_comm m n, pow_mul]
      exact Γ.pow_mem (hsn a ha) m

theorem nilpotent_arbitrary_roots_uniform_of_fg (Γ K : Subgroup G) (hK : K.FG)
    (hr : ∀ g ∈ K, g ∈ positiveSubgroupRoots Γ) :
    ∃ n : ℕ, 0 < n ∧ ∀ g ∈ K, g ^ n ∈ Γ := by
  letI : Group.FG K := (Group.fg_iff_subgroup_fg K).mpr hK
  obtain ⟨s, hs, hsf⟩ := Group.fg_iff.mp (inferInstance : Group.FG K)
  have hroots : ∀ k ∈ s, k ∈ positiveSubgroupRoots (Γ.subgroupOf K) := by
    intro k _
    obtain ⟨n, hn, hp⟩ := hr k.val k.property
    exact ⟨n, hn, hp⟩
  obtain ⟨N, hN, hp⟩ := finite_positiveRoots_common_power (Γ.subgroupOf K) s hsf hroots
  obtain ⟨n, hn, hall⟩ := nilpotent_power_generators_uniform (Γ.subgroupOf K) s hsf hs N hN hp
  exact ⟨n, hn, fun g hg => hall (⟨g, hg⟩ : K)⟩

theorem nilpotentArbitraryPositiveRootSubgroup_least (Γ H : Subgroup G)
    (hΓ : Γ ≤ H) (hroot : ∀ (g : G) (n : ℕ), 0 < n → g ^ n ∈ H → g ∈ H) :
    nilpotentArbitraryPositiveRootSubgroup Γ ≤ H := by
  intro g hg
  obtain ⟨n, hn, hp⟩ := hg
  exact hroot g n hn (hΓ hp)

theorem nilpotentArbitraryPositiveRootSubgroup_idempotent (Γ : Subgroup G) :
    nilpotentArbitraryPositiveRootSubgroup (nilpotentArbitraryPositiveRootSubgroup Γ) =
      nilpotentArbitraryPositiveRootSubgroup Γ := by
  apply le_antisymm
  · intro g hg
    obtain ⟨n, hn, hp⟩ := hg
    exact nilpotentArbitraryPositiveRootSubgroup_root Γ hn hp
  · exact nilpotentArbitraryPositiveRootSubgroup_contains _

end Hindman168
