import Hindman168.NilpotentPositiveRoots
import Hindman168.LowerCentralGeneratorPowers

/-! A finite set of positive-power generators modulo a genuinely normal
relative subgroup gives a finite actual quotient in a nilpotent group.
Normality is required only in the specified containing subgroup K. -/

namespace Hindman168
open Set Subgroup

variable {G : Type*} [Group G] [Group.IsNilpotent G]

theorem finite_relative_power_generator_quotient (H K : Subgroup G)
    [(H.subgroupOf K).Normal] (s : Set G) (hs : s.Finite)
    (hK : K = Subgroup.closure s ⊔ H)
    (hp : ∀ a ∈ s, ∃ n : ℕ, 0 < n ∧ a ^ n ∈ H) :
    Finite (K ⧸ H.subgroupOf K) := by
  let q := QuotientGroup.mk' (H.subgroupOf K)
  let R : Set K := K.subtype ⁻¹' s
  let U := Subgroup.closure (q '' R)
  have hR : R.Finite := Set.Finite.preimage Subtype.val_injective.injOn hs
  letI : Finite U := nilpotent_finite_closure_of_torsion (q '' R) (hR.image q) (by
    rintro x ⟨a, ha, rfl⟩
    obtain ⟨n, hn, hpow⟩ := hp a.val ha
    apply isOfFinOrder_iff_pow_eq_one.mpr
    exact ⟨n, hn, (q.map_pow a n).symm.trans
      ((QuotientGroup.eq_one_iff (a ^ n)).mpr hpow)⟩)
  let P := U.comap q
  have hsK : Subgroup.closure s ≤ K := by rw [hK]; exact le_sup_left
  have hHK : H ≤ K := by rw [hK]; exact le_sup_right
  have hsP : Subgroup.closure s ≤ P.map K.subtype := by
    apply (Subgroup.closure_le (K := P.map K.subtype)).mpr
    intro a ha
    let k : K := ⟨a, hsK (Subgroup.subset_closure ha)⟩
    exact ⟨k, Subgroup.subset_closure ⟨k, ha, rfl⟩, rfl⟩
  have hHP : H ≤ P.map K.subtype := by
    intro a ha
    let k : K := ⟨a, hHK ha⟩
    have he : q k = 1 := (QuotientGroup.eq_one_iff k).mpr ha
    have hk : k ∈ P := by
      change q k ∈ U
      rw [he]
      exact U.one_mem
    exact ⟨k, hk, rfl⟩
  have hKP : K ≤ P.map K.subtype := hK.le.trans (sup_le hsP hHP)
  have hP : P = ⊤ := by
    apply eq_top_iff.mpr
    intro k _
    obtain ⟨k', hk', he⟩ := hKP k.property
    have hk : k' = k := Subtype.ext he
    exact hk ▸ hk'
  have hU : U = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨k, rfl⟩ := (QuotientGroup.mk'_surjective _) x
    exact (show k ∈ P from hP.symm ▸ Subgroup.mem_top k)
  exact Finite.of_surjective U.subtype (by
    intro x
    exact ⟨⟨x, hU.symm ▸ Subgroup.mem_top x⟩, rfl⟩)

theorem relative_power_generators_uniform_power (H K : Subgroup G)
    [(H.subgroupOf K).Normal] (s : Set G) (hs : s.Finite)
    (hK : K = Subgroup.closure s ⊔ H)
    (hp : ∀ a ∈ s, ∃ n : ℕ, 0 < n ∧ a ^ n ∈ H) :
    ∃ n : ℕ, 0 < n ∧ ∀ g ∈ K, g ^ n ∈ H := by
  letI : Finite (K ⧸ H.subgroupOf K) :=
    finite_relative_power_generator_quotient H K s hs hK hp
  obtain ⟨n, hn, he⟩ :=
    (Monoid.ExponentExists.of_finite : Monoid.ExponentExists (K ⧸ H.subgroupOf K))
  refine ⟨n, hn, ?_⟩
  intro g hg
  let k : K := ⟨g, hg⟩
  exact (QuotientGroup.eq_one_iff (k ^ n)).mp
    (((QuotientGroup.mk' (H.subgroupOf K)).map_pow k n).trans (he _))

end Hindman168
