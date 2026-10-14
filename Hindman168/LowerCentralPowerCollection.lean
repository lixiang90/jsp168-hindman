import Hindman168.ClassTwoPositiveRoots

/-! Exact collection in genuine successive lower-central quotients.
An original direction in layer j gives a central commutator modulo
layer j+2. Power collection and the two-denominator root product therefore
hold in that actual quotient. The original product lands in Gamma joined
with the actual remaining layer, not necessarily back in Gamma itself. -/

namespace Hindman168
open Set Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem lowerCentral_mem_center_quotient_next (j : ℕ) {x : G}
    (hx : x ∈ (⊤ : Subgroup G).lowerCentralSeries (j + 1)) :
    (QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (j + 2))) x ∈
      Subgroup.center (G ⧸ (⊤ : Subgroup G).lowerCentralSeries (j + 2)) := by
  let q := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (j + 2))
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨g, rfl⟩ := (QuotientGroup.mk'_surjective _) y
  apply (commutatorElement_eq_one_iff_mul_comm.mp ?_).symm
  rw [← map_commutatorElement q]
  apply (QuotientGroup.eq_one_iff ⁅x, g⁆).mpr
  exact Subgroup.commutator_mem_commutator hx (Subgroup.mem_top g)

theorem lowerCentral_commutator_quotient_central (j : ℕ) {a : G}
    (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries j) (b : G) :
    ⁅(QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (j + 2))) a,
      (QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (j + 2))) b⁆ ∈
        Subgroup.center (G ⧸ (⊤ : Subgroup G).lowerCentralSeries (j + 2)) := by
  rw [← map_commutatorElement]
  exact lowerCentral_mem_center_quotient_next j
    (Subgroup.commutator_mem_commutator ha (Subgroup.mem_top b))

theorem lowerCentral_commutator_powers_quotient (j : ℕ) {a : G}
    (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries j) (b : G) (m n : ℕ) :
    (QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (j + 2))) ⁅a ^ m, b ^ n⁆ =
      (QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (j + 2)))
        (⁅a, b⁆ ^ (m * n)) := by
  let q := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (j + 2))
  have hc := lowerCentral_commutator_quotient_central j ha b
  have hp := commutator_nat_powers_of_central (q a) (q b) hc m n
  simpa only [map_commutatorElement, map_pow] using hp

theorem lowerCentral_product_double_power_mem_sup (Γ : Subgroup G)
    (j : ℕ) {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries j)
    (b : G) (m n : ℕ) (ham : a ^ m ∈ Γ) (hbn : b ^ n ∈ Γ) :
    (a * b) ^ (2 * (m * n)) ∈ Γ ⊔ (⊤ : Subgroup G).lowerCentralSeries (j + 2) := by
  let q := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (j + 2))
  have hqa : (q a) ^ m ∈ Γ.map q := by
    rw [← q.map_pow]
    exact ⟨a ^ m, ham, rfl⟩
  have hqb : (q b) ^ n ∈ Γ.map q := by
    rw [← q.map_pow]
    exact ⟨b ^ n, hbn, rfl⟩
  have hp : (q (a * b)) ^ (2 * (m * n)) ∈ Γ.map q := by
    rw [q.map_mul]
    exact subgroup_product_double_power_of_central_commutator (Γ.map q)
      (q a) (q b) (lowerCentral_commutator_quotient_central j ha b) m n hqa hqb
  have hm : (a * b) ^ (2 * (m * n)) ∈ (Γ.map q).comap q := by
    change q ((a * b) ^ (2 * (m * n))) ∈ Γ.map q
    rw [q.map_pow]
    exact hp
  have he : (Γ.map q).comap q = Γ ⊔ (⊤ : Subgroup G).lowerCentralSeries (j + 2) := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  exact he ▸ hm

end Hindman168
