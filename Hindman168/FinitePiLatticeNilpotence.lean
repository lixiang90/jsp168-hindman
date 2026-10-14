import Hindman168.PiCosetQuotient
import Hindman168.FiniteDeterminedArrayLattice
import Mathlib.GroupTheory.Nilpotent

namespace Hindman168

theorem piGroup_lowerCentral_bot {ι : Type*} (G : ι → Type*) [∀ i, Group (G i)]
    (s : ℕ) (hs : ∀ i, (⊤ : Subgroup (G i)).lowerCentralSeries s = ⊥) :
    (⊤ : Subgroup (∀ i, G i)).lowerCentralSeries s = ⊥ := by
  apply le_bot_iff.mp
  intro g hg
  apply Subgroup.mem_bot.mpr
  funext i
  have hpi := Subgroup.top_lowerCentralSeries_pi_le (Gs := G) s hg
  have hi := (Subgroup.mem_pi Set.univ).mp hpi i (Set.mem_univ i)
  rw [hs i] at hi
  exact Subgroup.mem_bot.mp hi

theorem piGroup_nilpotencyClass_le {ι : Type*} (G : ι → Type*) [∀ i, Group (G i)]
    (s : ℕ) (hs : ∀ i, (⊤ : Subgroup (G i)).lowerCentralSeries s = ⊥) :
    Group.nilpotencyClass (∀ i, G i) ≤ s := by
  letI : Group.IsNilpotent (∀ i, G i) := Subgroup.nilpotent_iff_lowerCentralSeries.mpr
    ⟨s, piGroup_lowerCentral_bot G s hs⟩
  exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp (piGroup_lowerCentral_bot G s hs)

theorem finitePiSubgroup_discrete {ι : Type*} [Finite ι] {G : ι → Type*}
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] (Γ : ∀ i, Subgroup (G i))
    [∀ i, DiscreteTopology (Γ i)] : DiscreteTopology (Subgroup.pi Set.univ Γ) := by
  let f : Subgroup.pi Set.univ Γ → ∀ i, Γ i :=
    fun g i => ⟨g.val i, (Subgroup.mem_pi Set.univ).mp g.property i (Set.mem_univ i)⟩
  apply discreteTopology_of_continuous_injective f
  · exact continuous_pi (fun i => ((continuous_apply i).comp continuous_subtype_val).subtype_mk _)
  · intro g h he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)

end Hindman168

