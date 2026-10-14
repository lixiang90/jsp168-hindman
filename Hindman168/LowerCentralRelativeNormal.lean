import Hindman168.FiniteRelativePowerQuotient

/-! Actual successive joins Gamma joined with lower-central layers.
Each next join is normal in its preceding join, although Gamma itself
need not be normal in G. This is proved from the genuine quotient maps. -/

namespace Hindman168
open Set Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem lowerCentral_mem_center_quotient_succ (j : ℕ) {x : G}
    (hx : x ∈ (⊤ : Subgroup G).lowerCentralSeries j) :
    (QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (j + 1))) x ∈
      Subgroup.center (G ⧸ (⊤ : Subgroup G).lowerCentralSeries (j + 1)) := by
  let q := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (j + 1))
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨g, rfl⟩ := (QuotientGroup.mk'_surjective _) y
  apply (commutatorElement_eq_one_iff_mul_comm.mp ?_).symm
  rw [← map_commutatorElement q]
  apply (QuotientGroup.eq_one_iff ⁅x, g⁆).mpr
  exact Subgroup.commutator_mem_commutator hx (Subgroup.mem_top g)

theorem lowerCentral_join_next_normal (Γ : Subgroup G) (j : ℕ) :
    ((Γ ⊔ (⊤ : Subgroup G).lowerCentralSeries (j + 1)).subgroupOf
      (Γ ⊔ (⊤ : Subgroup G).lowerCentralSeries j)).Normal := by
  let K := Γ ⊔ (⊤ : Subgroup G).lowerCentralSeries j
  let H := Γ ⊔ (⊤ : Subgroup G).lowerCentralSeries (j + 1)
  let q := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (j + 1))
  have hHK : H ≤ K :=
    sup_le_sup_left ((⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ j)) Γ
  have hC : ((⊤ : Subgroup G).lowerCentralSeries j).map q ≤
      Subgroup.center (G ⧸ (⊤ : Subgroup G).lowerCentralSeries (j + 1)) := by
    rintro x ⟨g, hg, rfl⟩
    exact lowerCentral_mem_center_quotient_succ j hg
  have hcomm : ⁅K, K⁆ ≤ H := by
    have hm : (⁅K, K⁆).map q ≤ Γ.map q := by
      rw [Subgroup.map_commutator]
      have hKmap : K.map q = Γ.map q ⊔ ((⊤ : Subgroup G).lowerCentralSeries j).map q :=
        Subgroup.map_sup _ _ _
      rw [hKmap, commutator_sup_central_left_eq _ _ _ hC,
        Subgroup.commutator_comm, commutator_sup_central_left_eq _ _ _ hC]
      apply Subgroup.commutator_le.mpr
      intro a ha b hb
      rw [commutatorElement_def]
      exact (Γ.map q).mul_mem ((Γ.map q).mul_mem ((Γ.map q).mul_mem ha hb)
        ((Γ.map q).inv_mem ha)) ((Γ.map q).inv_mem hb)
    have he : (Γ.map q).comap q = H := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact he ▸ ((Subgroup.map_le_iff_le_comap).mp hm)
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mpr
  apply Subgroup.le_normalizer_iff_commutator_le_right.mpr
  exact (Subgroup.commutator_mono le_rfl hHK).trans hcomm

end Hindman168
