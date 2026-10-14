import Hindman168.NativeLieIdealSubgroup
import Hindman168.NativeLieSubalgebraTopology

/-! Actual original native Lie lower-central layers exponentiate to
genuine closed normal contractible subgroups of the original group.
These subgroups are not yet asserted equal to the original group lower
central series; that requires an additional two-way comparison. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieLowerCentralSubgroup (j : ℕ) : Subgroup G :=
  nativeLieSubalgebraSubgroup (E := E)
    (LieIdeal.toLieSubalgebra ℝ (GroupLieAlgebra I G)
      (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) j))

 theorem nativeLieLowerCentralSubgroup_mem_iff (j : ℕ) (g : G) :
    g ∈ nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) j ↔
      ∃ v : E, v ∈ nativeLieLowerCentralModel (I := I) (G := G) j ∧
        nativeLieExponential (I := I) (G := G) v = g := Iff.rfl

 theorem nativeLieLowerCentralSubgroup_antitone :
    Antitone (nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G)) := by
  intro i j hij g hg
  obtain ⟨v, hv, rfl⟩ := hg
  exact ⟨v, nativeLieLowerCentralModel_antitone (I := I) (G := G) hij hv, rfl⟩

 theorem nativeLieLowerCentralSubgroup_terminal :
    nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) (Group.nilpotencyClass G) = ⊥ := by
  apply le_antisymm
  · rintro g ⟨v, hv, rfl⟩
    have hv0 : v = 0 := by
      change v ∈ nativeLieLowerCentralModel (I := I) (G := G) (Group.nilpotencyClass G) at hv
      rw [nativeLieLowerCentralModel_nilpotencyClass_bot, Submodule.mem_bot] at hv
      exact hv
    let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
    change exp v = 1
    rw [hv0]
    exact nativeLieExponential_zero (I := I) (G := G)
  · exact bot_le

variable [ConnectedSpace G]

 theorem nativeLieLowerCentralSubgroup_zero :
    nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) 0 = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨v, rfl⟩ := nativeLieExponential_surjective (E := E) (I := I) (G := G) g
  refine ⟨v, ?_, rfl⟩
  change v ∈ nativeLieLowerCentralModel (I := I) (G := G) 0
  rw [nativeLieLowerCentralModel_zero]
  trivial

 theorem nativeLieLowerCentralSubgroup_normal (j : ℕ) :
    (nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) j).Normal :=
  nativeLieIdealSubgroup_normal
    (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) j)

variable [SimplyConnectedSpace G]

 theorem nativeLieLowerCentralSubgroup_closed (j : ℕ) :
    IsClosed (nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) j : Set G) :=
  nativeLieSubalgebraSubgroup_closed
    (LieIdeal.toLieSubalgebra ℝ (GroupLieAlgebra I G)
      (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) j))

 theorem nativeLieLowerCentralSubgroup_contractible (j : ℕ) :
    ContractibleSpace (nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) j) :=
  nativeLieSubalgebraSubgroup_contractible
    (LieIdeal.toLieSubalgebra ℝ (GroupLieAlgebra I G)
      (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) j))

 theorem nativeLieLowerCentralSubgroup_simplyConnected (j : ℕ) :
    SimplyConnectedSpace (nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) j) :=
  nativeLieSubalgebraSubgroup_simplyConnected
    (LieIdeal.toLieSubalgebra ℝ (GroupLieAlgebra I G)
      (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) j))

 theorem nativeLieLowerCentralSubgroup_mem_globalLogarithm_iff (j : ℕ) (g : G) :
    g ∈ nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) j ↔
      nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈
        nativeLieLowerCentralModel (E := E) (I := I) (G := G) j :=
  nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff
    (LieIdeal.toLieSubalgebra ℝ (GroupLieAlgebra I G)
      (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) j)) g

end Hindman168
