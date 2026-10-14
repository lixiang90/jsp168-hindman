import Hindman168.AlignmentPolynomialModelArrays

namespace Hindman168

theorem alignmentJointArrayGroup_lowerCentral_bot {ι : Type*}
    (σ G : ι → Type*) [∀ a, Group (G a)] (s : ℕ)
    (hG : ∀ a, (⊤ : Subgroup (G a)).lowerCentralSeries s = ⊥) :
    (⊤ : Subgroup (∀ a, alignmentPolynomialArrayGroup (σ a) (G a))).lowerCentralSeries s = ⊥ := by
  apply le_bot_iff.mp
  intro f hf
  apply Subgroup.mem_bot.mpr
  funext a
  have hpi : (⊤ : Subgroup (∀ a, alignmentPolynomialArrayGroup (σ a) (G a))).lowerCentralSeries s ≤
      Subgroup.pi Set.univ (fun a =>
        (⊤ : Subgroup (alignmentPolynomialArrayGroup (σ a) (G a))).lowerCentralSeries s) :=
    Subgroup.top_lowerCentralSeries_pi_le s
  have hfa := (Subgroup.mem_pi Set.univ).mp (hpi hf) a (Set.mem_univ a)
  rw [alignmentPolynomialArrayGroup_lowerCentral_bot s (hG a)] at hfa
  exact Subgroup.mem_bot.mp hfa

theorem alignmentJointArrayGroup_nilpotent {ι : Type*}
    (σ G : ι → Type*) [∀ a, Group (G a)] (s : ℕ)
    (hG : ∀ a, (⊤ : Subgroup (G a)).lowerCentralSeries s = ⊥) :
    Group.IsNilpotent (∀ a, alignmentPolynomialArrayGroup (σ a) (G a)) :=
  Subgroup.nilpotent_iff_lowerCentralSeries.mpr
    ⟨s, alignmentJointArrayGroup_lowerCentral_bot σ G s hG⟩

theorem alignmentJointArrayGroup_nilpotencyClass_le {ι : Type*}
    (σ G : ι → Type*) [∀ a, Group (G a)] (s : ℕ)
    (hG : ∀ a, (⊤ : Subgroup (G a)).lowerCentralSeries s = ⊥) :
    Group.nilpotencyClass (∀ a, alignmentPolynomialArrayGroup (σ a) (G a)) ≤ s := by
  letI := alignmentJointArrayGroup_nilpotent σ G s hG
  exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
    (alignmentJointArrayGroup_lowerCentral_bot σ G s hG)

end Hindman168
