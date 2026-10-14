import Hindman168.LowerCentralRelativeNormal

/-! Elimination of all genuine lower-central remainders. Finite generators
whose common positive power lies in an arbitrary specified subgroup
yield a uniform positive power for the entire original nilpotent group.
The specified subgroup is not assumed normal. -/

namespace Hindman168
open Set Subgroup

variable {G : Type*} [Group G] [Group.IsNilpotent G]

theorem lowerCentral_join_step_uniform_power (Γ : Subgroup G) (s : Set G)
    (hsf : s.Finite) (hs : Subgroup.closure s = ⊤)
    (N : ℕ) (hN : 0 < N) (hp : ∀ b ∈ s, b ^ N ∈ Γ) (j : ℕ) :
    ∃ n : ℕ, 0 < n ∧ ∀ g ∈ Γ ⊔ (⊤ : Subgroup G).lowerCentralSeries j,
      g ^ n ∈ Γ ⊔ (⊤ : Subgroup G).lowerCentralSeries (j + 1) := by
  let H := Γ ⊔ (⊤ : Subgroup G).lowerCentralSeries (j + 1)
  let K := Γ ⊔ (⊤ : Subgroup G).lowerCentralSeries j
  letI : (H.subgroupOf K).Normal := lowerCentral_join_next_normal Γ j
  apply relative_power_generators_uniform_power H K
    (lowerCentralCommutatorGenerators s j) (lowerCentralCommutatorGenerators_finite s hsf j)
  · calc
      K = Γ ⊔ (Subgroup.closure (lowerCentralCommutatorGenerators s j) ⊔
          (⊤ : Subgroup G).lowerCentralSeries (j + 1)) :=
        congrArg (fun A => Γ ⊔ A) (lowerCentral_generated_mod_next s hs j)
      _ = Subgroup.closure (lowerCentralCommutatorGenerators s j) ⊔ H :=
        sup_left_comm _ _ _
  · intro a ha
    exact ⟨N ^ (j + 1), pow_pos hN _,
      lowerCentral_generator_power_mem_sup Γ s N hp j a ha⟩

theorem lowerCentral_joins_uniform_power_of_terminating (Γ : Subgroup G) (s : Set G)
    (hsf : s.Finite) (hs : Subgroup.closure s = ⊤)
    (N : ℕ) (hN : 0 < N) (hp : ∀ b ∈ s, b ^ N ∈ Γ)
    (j k : ℕ) (hk : (⊤ : Subgroup G).lowerCentralSeries (j + k) = ⊥) :
    ∃ n : ℕ, 0 < n ∧ ∀ g ∈ Γ ⊔ (⊤ : Subgroup G).lowerCentralSeries j, g ^ n ∈ Γ := by
  induction k generalizing j with
  | zero =>
    refine ⟨1, Nat.zero_lt_one, ?_⟩
    intro g hg
    have hbot : (⊤ : Subgroup G).lowerCentralSeries j = ⊥ := by
      simpa only [Nat.add_zero] using hk
    simpa only [hbot, sup_bot_eq, pow_one] using hg
  | succ k ih =>
    obtain ⟨e, he, hstep⟩ := lowerCentral_join_step_uniform_power Γ s hsf hs N hN hp j
    obtain ⟨f, hf, htail⟩ := ih (j + 1) (by
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hk)
    refine ⟨e * f, Nat.mul_pos he hf, ?_⟩
    intro g hg
    rw [pow_mul]
    exact htail (g ^ e) (hstep g hg)

theorem nilpotent_power_generators_uniform (Γ : Subgroup G) (s : Set G)
    (hsf : s.Finite) (hs : Subgroup.closure s = ⊤)
    (N : ℕ) (hN : 0 < N) (hp : ∀ b ∈ s, b ^ N ∈ Γ) :
    ∃ n : ℕ, 0 < n ∧ ∀ g : G, g ^ n ∈ Γ := by
  obtain ⟨n, hn, hall⟩ := lowerCentral_joins_uniform_power_of_terminating Γ s hsf hs N hN hp
    0 (Group.nilpotencyClass G)
    (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (by simp only [Nat.zero_add, le_refl]))
  refine ⟨n, hn, fun g => hall g ?_⟩
  simp only [Subgroup.lowerCentralSeries_zero, sup_top_eq, Subgroup.mem_top]

end Hindman168
