import Hindman168.NativeLieAdjointLayer

/-! Actual commutators with an exponential native lower-central layer
belong to its next layer. This proves one direction of comparison with
the original group lower central series. Equality and algebraic group
layer closedness require the reverse inclusion and are not assumed. -/

namespace Hindman168
open Function Set
open scoped Manifold ContDiff commutatorElement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieCommutator_exponential_mem_lowerCentral_next
    (g : G) {v : E} {j : ℕ}
    (hv : v ∈ nativeLieLowerCentralModel (I := I) (G := G) j) :
    ⁅g, nativeLieExponential (I := I) (G := G) v⁆ ∈
      nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) (j + 1) := by
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  let u : E := nativeLieAdjoint (I := I) g v
  have hn : -v ∈ nativeLieLowerCentralModel (I := I) (G := G) j :=
    Submodule.neg_mem _ hv
  have hs : u + -v ∈ nativeLieLowerCentralModel (I := I) (G := G) (j + 1) := by
    simpa only [sub_eq_add_neg] using nativeLieAdjoint_sub_mem_lowerCentral_next g hv
  have hp : exp u * exp (-v) ∈
      nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) (j + 1) :=
    nativeLieExponential_product_mem_lowerCentral_next hn hs
  have hc : g * exp v * g⁻¹ = exp u :=
    nativeLieAdjoint_exponential_conjugation (I := I) g v
  have hi : exp (-v) = (exp v)⁻¹ := nativeLieExponential_neg (I := I) (G := G) v
  change ⁅g, exp v⁆ ∈ _
  rw [commutatorElement_def, hc, ← hi]
  exact hp

 theorem nativeLieLowerCentralSubgroup_commutator_le_next (j : ℕ) :
    ⁅(⊤ : Subgroup G), nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) j⁆ ≤
      nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) (j + 1) := by
  apply Subgroup.commutator_le.mpr
  rintro g _ a ⟨v, hv, rfl⟩
  exact nativeLieCommutator_exponential_mem_lowerCentral_next g hv

 theorem nativeGroupLowerCentralSeries_le_exponential (j : ℕ) :
    (⊤ : Subgroup G).lowerCentralSeries j ≤
      nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) j := by
  induction j with
  | zero => rw [Subgroup.lowerCentralSeries_zero, nativeLieLowerCentralSubgroup_zero]
  | succ j ih =>
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl ih).trans
      (nativeLieLowerCentralSubgroup_commutator_le_next (E := E) (I := I) (G := G) j)

end Hindman168
