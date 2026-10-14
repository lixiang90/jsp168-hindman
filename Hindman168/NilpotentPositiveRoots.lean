import Hindman168.NilpotentTorsionClosure
import Hindman168.PositiveSubgroupRoots

/-! Finite-order elements form a genuine normal subgroup of an arbitrary
actual nilpotent group. Its inverse image under an actual normal quotient
is precisely the positive roots of the specified normal subgroup.
No normality is assumed of the lattice in the full prize target. -/

namespace Hindman168
open Set Subgroup

variable {G : Type*} [Group G] [Group.IsNilpotent G]

def nilpotentTorsionSubgroup (G : Type*) [Group G] [Group.IsNilpotent G] : Subgroup G where
  carrier := {g | IsOfFinOrder g}
  one_mem' := IsOfFinOrder.one
  mul_mem' := fun ha hb => nilpotent_finiteOrder_mul ha hb
  inv_mem' := fun ha => ha.inv

theorem nilpotentTorsionSubgroup_mem_iff (g : G) :
    g ∈ nilpotentTorsionSubgroup G ↔ IsOfFinOrder g := Iff.rfl

instance nilpotentTorsionSubgroup_normal : (nilpotentTorsionSubgroup G).Normal where
  conj_mem := by
    intro g hg a
    obtain ⟨n, hn, he⟩ := hg.exists_pow_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    rw [conj_pow, he]
    simp

def normalPositiveRootSubgroup (Γ : Subgroup G) [Γ.Normal] : Subgroup G :=
  (nilpotentTorsionSubgroup (G ⧸ Γ)).comap (QuotientGroup.mk' Γ)

theorem normalPositiveRootSubgroup_mem_iff (Γ : Subgroup G) [Γ.Normal] (g : G) :
    g ∈ normalPositiveRootSubgroup Γ ↔ g ∈ positiveSubgroupRoots Γ := by
  let q := QuotientGroup.mk' Γ
  change IsOfFinOrder (q g) ↔ _
  constructor
  · intro hg
    obtain ⟨n, hn, he⟩ := hg.exists_pow_eq_one
    refine ⟨n, hn, (QuotientGroup.eq_one_iff (g ^ n)).mp ?_⟩
    exact (q.map_pow g n).trans he
  · rintro ⟨n, hn, he⟩
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    exact (q.map_pow g n).symm.trans ((QuotientGroup.eq_one_iff (g ^ n)).mpr he)

theorem positiveSubgroupRoots_mul_of_normal (Γ : Subgroup G) [Γ.Normal] {g h : G}
    (hg : g ∈ positiveSubgroupRoots Γ) (hh : h ∈ positiveSubgroupRoots Γ) :
    g * h ∈ positiveSubgroupRoots Γ :=
  (normalPositiveRootSubgroup_mem_iff Γ (g * h)).mp
    ((normalPositiveRootSubgroup Γ).mul_mem
      ((normalPositiveRootSubgroup_mem_iff Γ g).mpr hg)
      ((normalPositiveRootSubgroup_mem_iff Γ h).mpr hh))

theorem normalPositiveRootSubgroup_normal (Γ : Subgroup G) [Γ.Normal] :
    (normalPositiveRootSubgroup Γ).Normal := by
  unfold normalPositiveRootSubgroup
  infer_instance

theorem normalPositiveRootSubgroup_root (Γ : Subgroup G) [Γ.Normal] {g : G} {n : ℕ}
    (hn : 0 < n) (hg : g ^ n ∈ normalPositiveRootSubgroup Γ) :
    g ∈ normalPositiveRootSubgroup Γ :=
  (normalPositiveRootSubgroup_mem_iff Γ g).mpr
    (positiveSubgroupRoots_root Γ hn ((normalPositiveRootSubgroup_mem_iff Γ (g ^ n)).mp hg))

attribute [local instance] normalPositiveRootSubgroup_normal

theorem normalPositiveRoot_quotient_finiteOrder_iff (Γ : Subgroup G) [Γ.Normal]
    (x : G ⧸ normalPositiveRootSubgroup Γ) : IsOfFinOrder x ↔ x = 1 := by
  constructor
  · refine QuotientGroup.induction_on x ?_
    intro g hg
    obtain ⟨n, hn, he⟩ := hg.exists_pow_eq_one
    apply (QuotientGroup.eq_one_iff g).mpr
    apply normalPositiveRootSubgroup_root Γ hn
    apply (QuotientGroup.eq_one_iff (g ^ n)).mp
    exact ((QuotientGroup.mk' (normalPositiveRootSubgroup Γ)).map_pow g n).trans he
  · intro hx
    rw [hx]
    exact IsOfFinOrder.one

theorem finite_normal_root_quotient_of_fg (Γ : Subgroup G) [Γ.Normal]
    (K : Subgroup G) (hK : K.FG) (hr : K ≤ normalPositiveRootSubgroup Γ) :
    Finite (K ⧸ Γ.subgroupOf K) := by
  letI : Group.FG K := (Group.fg_iff_subgroup_fg K).mpr hK
  let q := QuotientGroup.mk' (Γ.subgroupOf K)
  letI : Group.FG (K ⧸ Γ.subgroupOf K) := Group.fg_of_surjective (QuotientGroup.mk'_surjective (Γ.subgroupOf K))
  apply nilpotent_finite_of_fg_torsion
  intro x
  refine QuotientGroup.induction_on x ?_
  intro k
  obtain ⟨n, hn, he⟩ := (normalPositiveRootSubgroup_mem_iff Γ k.val).mp (hr k.property)
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨n, hn, ?_⟩
  apply (q.map_pow k n).symm.trans
  exact (QuotientGroup.eq_one_iff (k ^ n)).mpr he

theorem normal_roots_uniform_positive_power_of_fg (Γ : Subgroup G) [Γ.Normal]
    (K : Subgroup G) (hK : K.FG) (hr : K ≤ normalPositiveRootSubgroup Γ) :
    ∃ n : ℕ, 0 < n ∧ ∀ g ∈ K, g ^ n ∈ Γ := by
  letI : Finite (K ⧸ Γ.subgroupOf K) := finite_normal_root_quotient_of_fg Γ K hK hr
  obtain ⟨n, hn, he⟩ :=
    (Monoid.ExponentExists.of_finite : Monoid.ExponentExists (K ⧸ Γ.subgroupOf K))
  refine ⟨n, hn, ?_⟩
  intro g hg
  let k : K := ⟨g, hg⟩
  have hq : (QuotientGroup.mk' (Γ.subgroupOf K)) (k ^ n) = 1 :=
    ((QuotientGroup.mk' (Γ.subgroupOf K)).map_pow k n).trans (he _)
  exact (QuotientGroup.eq_one_iff (k ^ n)).mp hq

end Hindman168
