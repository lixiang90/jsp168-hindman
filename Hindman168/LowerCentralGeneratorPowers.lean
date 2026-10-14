import Hindman168.LowerCentralFiniteGenerators

/-! Powers of actual iterated generator commutators return to Gamma
modulo the next actual layer. Gamma is arbitrary and need not be normal.
The central remainder is used inside the next quotient, never discarded. -/

namespace Hindman168
open Set Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem lowerCentral_commutator_power_mem_sup (Γ : Subgroup G)
    (j : ℕ) {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries j)
    (b : G) (m n : ℕ)
    (ham : a ^ m ∈ Γ ⊔ (⊤ : Subgroup G).lowerCentralSeries (j + 1))
    (hbn : b ^ n ∈ Γ) :
    ⁅a, b⁆ ^ (m * n) ∈ Γ ⊔ (⊤ : Subgroup G).lowerCentralSeries (j + 2) := by
  let q := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (j + 2))
  obtain ⟨γ, hγ, z, hz, hprod⟩ := Subgroup.mem_sup_of_normal_right.mp ham
  have hΓ : ⁅γ, b ^ n⁆ ∈ Γ := by
    rw [commutatorElement_def]
    exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hγ hbn) (Γ.inv_mem hγ)) (Γ.inv_mem hbn)
  have hc : q ⁅a ^ m, b ^ n⁆ ∈ Γ.map q := by
    rw [← hprod, map_commutatorElement, q.map_mul,
      commutator_right_central_multiplier_left (q γ) (q (b ^ n)) (q z)
        (lowerCentral_mem_center_quotient_next j hz)]
    rw [← map_commutatorElement]
    exact ⟨⁅γ, b ^ n⁆, hΓ, rfl⟩
  have hm : q (⁅a, b⁆ ^ (m * n)) ∈ Γ.map q :=
    (lowerCentral_commutator_powers_quotient j ha b m n) ▸ hc
  have he : (Γ.map q).comap q =
      Γ ⊔ (⊤ : Subgroup G).lowerCentralSeries (j + 2) := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  exact he ▸ (show ⁅a, b⁆ ^ (m * n) ∈ (Γ.map q).comap q from hm)

theorem lowerCentral_generator_power_mem_sup (Γ : Subgroup G) (s : Set G)
    (N : ℕ) (hN : ∀ b ∈ s, b ^ N ∈ Γ) (j : ℕ) :
    ∀ a ∈ lowerCentralCommutatorGenerators s j,
      a ^ (N ^ (j + 1)) ∈ Γ ⊔ (⊤ : Subgroup G).lowerCentralSeries (j + 1) := by
  induction j with
  | zero =>
    intro a ha
    exact Subgroup.mem_sup_left (by simpa only [Nat.zero_add, pow_one] using hN a ha)
  | succ j ih =>
    rintro a ⟨x, hx, b, hb, rfl⟩
    have hm := lowerCentral_commutator_power_mem_sup Γ j
      (lowerCentralCommutatorGenerators_subset s j hx) b (N ^ (j + 1)) N
      (ih x hx) (hN b hb)
    simpa only [pow_succ] using hm

end Hindman168
