import Hindman168.LowerCentralPowerCollection
import Hindman168.CentralCommutatorGeneration

/-! Actual iterated generator commutators generate every successive
lower-central factor. The next original layer is retained exactly.
No finite generation of the whole original lower layer is assumed. -/

namespace Hindman168
open Set Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

def lowerCentralCommutatorGenerators (s : Set G) : ℕ → Set G
  | 0 => s
  | j + 1 => {g | ∃ a ∈ lowerCentralCommutatorGenerators s j, ∃ b ∈ s, ⁅a, b⁆ = g}

theorem lowerCentralCommutatorGenerators_finite (s : Set G) (hs : s.Finite) (j : ℕ) :
    (lowerCentralCommutatorGenerators s j).Finite := by
  induction j with
  | zero => exact hs
  | succ j ih => exact commutator_pairs_finite _ s ih hs

theorem lowerCentralCommutatorGenerators_subset (s : Set G) (j : ℕ) :
    lowerCentralCommutatorGenerators s j ⊆ (⊤ : Subgroup G).lowerCentralSeries j := by
  induction j with
  | zero => exact fun _ _ => Subgroup.mem_top _
  | succ j ih =>
    rintro g ⟨a, ha, b, _, rfl⟩
    exact Subgroup.commutator_mem_commutator (ih ha) (Subgroup.mem_top b)

theorem lowerCentral_generator_step_mod_next (j : ℕ) (s t : Set G)
    (hs : (⊤ : Subgroup G).lowerCentralSeries j =
      Subgroup.closure s ⊔ (⊤ : Subgroup G).lowerCentralSeries (j + 1))
    (ht : Subgroup.closure t = ⊤) :
    (⊤ : Subgroup G).lowerCentralSeries (j + 1) =
      Subgroup.closure {g | ∃ a ∈ s, ∃ b ∈ t, ⁅a, b⁆ = g} ⊔
        (⊤ : Subgroup G).lowerCentralSeries (j + 2) := by
  let q := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (j + 2))
  let T : Set G := {g | ∃ a ∈ s, ∃ b ∈ t, ⁅a, b⁆ = g}
  have htq : Subgroup.closure (q '' t) = ⊤ := by
    rw [← MonoidHom.map_closure, ht]
    exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)
  have hsl : Subgroup.closure s ≤ (⊤ : Subgroup G).lowerCentralSeries j := by
    rw [hs]
    exact le_sup_left
  have hsq : Subgroup.closure (q '' s) ≤
      ((⊤ : Subgroup G).lowerCentralSeries j).map q := by
    rw [← MonoidHom.map_closure]
    exact Subgroup.map_mono hsl
  have htail : ((⊤ : Subgroup G).lowerCentralSeries (j + 1)).map q ≤
      Subgroup.center (G ⧸ (⊤ : Subgroup G).lowerCentralSeries (j + 2)) := by
    rintro x ⟨g, hg, rfl⟩
    exact lowerCentral_mem_center_quotient_next j hg
  have hc : ⁅Subgroup.closure (q '' s), Subgroup.closure (q '' t)⁆ ≤
      Subgroup.center (G ⧸ (⊤ : Subgroup G).lowerCentralSeries (j + 2)) := by
    rw [htq]
    apply Subgroup.commutator_le.mpr
    intro x hx y _
    obtain ⟨a, ha, rfl⟩ := hsq hx
    obtain ⟨b, rfl⟩ := (QuotientGroup.mk'_surjective _) y
    exact lowerCentral_commutator_quotient_central j ha b
  have hpairs : {g | ∃ a ∈ q '' s, ∃ b ∈ q '' t, ⁅a, b⁆ = g} = q '' T := by
    ext g
    constructor
    · rintro ⟨a, ⟨a', ha', rfl⟩, b, ⟨b', hb', rfl⟩, rfl⟩
      exact ⟨⁅a', b'⁆, ⟨a', ha', b', hb', rfl⟩, map_commutatorElement q a' b'⟩
    · rintro ⟨x, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      rw [map_commutatorElement]
      exact ⟨q a, ⟨a, ha, rfl⟩, q b, ⟨b, hb, rfl⟩, rfl⟩
  have hsmap : ((⊤ : Subgroup G).lowerCentralSeries j).map q =
      Subgroup.closure (q '' s) ⊔
        ((⊤ : Subgroup G).lowerCentralSeries (j + 1)).map q :=
    (congrArg (Subgroup.map q) hs).trans (by
      rw [Subgroup.map_sup, MonoidHom.map_closure])
  have he : ((⊤ : Subgroup G).lowerCentralSeries (j + 1)).map q =
      (Subgroup.closure T).map q := by
    calc
      _ = (⁅(⊤ : Subgroup G).lowerCentralSeries j, (⊤ : Subgroup G)⁆).map q :=
        congrArg (Subgroup.map q) ((⊤ : Subgroup G).lowerCentralSeries_succ j)
      _ = ⁅((⊤ : Subgroup G).lowerCentralSeries j).map q, ⊤⁆ := by
        rw [Subgroup.map_commutator,
          Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
      _ = ⁅Subgroup.closure (q '' s) ⊔
          ((⊤ : Subgroup G).lowerCentralSeries (j + 1)).map q, ⊤⁆ :=
        congrArg (fun H => ⁅H, ⊤⁆) hsmap
      _ = ⁅Subgroup.closure (q '' s), ⊤⁆ :=
        commutator_sup_central_left_eq _ _ _ htail
      _ = ⁅Subgroup.closure (q '' s), Subgroup.closure (q '' t)⁆ :=
        congrArg (fun H => ⁅Subgroup.closure (q '' s), H⁆) htq.symm
      _ = Subgroup.closure {g | ∃ a ∈ q '' s, ∃ b ∈ q '' t, ⁅a, b⁆ = g} :=
        commutator_closure_eq_closure_pairs_of_central _ _ hc
      _ = Subgroup.closure (q '' T) := congrArg Subgroup.closure hpairs
      _ = (Subgroup.closure T).map q := (MonoidHom.map_closure q T).symm
  have hec := congrArg (Subgroup.comap q) he
  rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hec
  have hl : (⊤ : Subgroup G).lowerCentralSeries (j + 2) ≤
      (⊤ : Subgroup G).lowerCentralSeries (j + 1) :=
    (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ (j + 1))
  rw [sup_eq_left.mpr hl] at hec
  exact hec

theorem lowerCentral_generated_mod_next (s : Set G)
    (hs : Subgroup.closure s = ⊤) (j : ℕ) :
    (⊤ : Subgroup G).lowerCentralSeries j =
      Subgroup.closure (lowerCentralCommutatorGenerators s j) ⊔
        (⊤ : Subgroup G).lowerCentralSeries (j + 1) := by
  induction j with
  | zero => simp only [Subgroup.lowerCentralSeries_zero, lowerCentralCommutatorGenerators, hs,
      top_sup_eq]
  | succ j ih =>
    exact lowerCentral_generator_step_mod_next j (lowerCentralCommutatorGenerators s j) s ih hs

theorem lowerCentral_factor_image_fg [Group.FG G] (j : ℕ) :
    (((⊤ : Subgroup G).lowerCentralSeries j).map
      (QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (j + 1)))).FG := by
  obtain ⟨s, hs, hsf⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let q := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (j + 1))
  have he := lowerCentral_generated_mod_next s hs j
  have hmap : (((⊤ : Subgroup G).lowerCentralSeries j).map q) =
      Subgroup.closure (q '' lowerCentralCommutatorGenerators s j) := by
    rw [he, Subgroup.map_sup, MonoidHom.map_closure]
    have hbot : (((⊤ : Subgroup G).lowerCentralSeries (j + 1)).map q) = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
    rw [hbot, sup_bot_eq]
  rw [hmap]
  exact (Subgroup.fg_iff _).mpr ⟨_, rfl,
    (lowerCentralCommutatorGenerators_finite s hsf j).image q⟩

theorem lowerCentral_fg_of_terminating (s : Set G) (hsf : s.Finite)
    (hs : Subgroup.closure s = ⊤) (j n : ℕ)
    (hn : (⊤ : Subgroup G).lowerCentralSeries (j + n) = ⊥) :
    ((⊤ : Subgroup G).lowerCentralSeries j).FG := by
  induction n generalizing j with
  | zero =>
    simpa only [Nat.add_zero] using (hn ▸ Subgroup.FG.bot :
      ((⊤ : Subgroup G).lowerCentralSeries (j + 0)).FG)
  | succ n ih =>
    have hnext : ((⊤ : Subgroup G).lowerCentralSeries (j + 1)).FG :=
      ih (j + 1) (by simpa only [Nat.add_assoc, Nat.add_comm 1 n] using hn)
    rw [lowerCentral_generated_mod_next s hs j]
    exact ((Subgroup.fg_iff _).mpr ⟨_, rfl,
      lowerCentralCommutatorGenerators_finite s hsf j⟩).sup hnext

theorem nilpotent_lowerCentral_fg [Group.FG G] [Group.IsNilpotent G] (j : ℕ) :
    ((⊤ : Subgroup G).lowerCentralSeries j).FG := by
  obtain ⟨s, hs, hsf⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  apply lowerCentral_fg_of_terminating s hsf hs j (Group.nilpotencyClass G)
  exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr
    (Nat.le_add_left (Group.nilpotencyClass G) j)

end Hindman168
