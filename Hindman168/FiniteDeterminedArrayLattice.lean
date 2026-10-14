import Hindman168.AlignmentPolynomialArrayLattice

/-! A pointwise lattice in any array subgroup determined by finitely many
evaluations is discrete in the inherited topology. No cocompactness is assumed. -/

namespace Hindman168

def pointwiseArrayLattice {Z G : Type*} [Group G]
    (A : Subgroup (Z → G)) (Γ : Subgroup G) : Subgroup A :=
  (Subgroup.pi Set.univ (fun _ : Z => Γ)).comap A.subtype

theorem pointwiseArrayLattice_mem {Z G : Type*} [Group G]
    (A : Subgroup (Z → G)) (Γ : Subgroup G) (a : A) :
    a ∈ pointwiseArrayLattice A Γ ↔ ∀ z, a.val z ∈ Γ := by
  simp only [pointwiseArrayLattice, Subgroup.mem_comap, Subgroup.mem_pi,
    Set.mem_univ, forall_const]
  rfl

theorem discreteTopology_of_continuous_injective {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [DiscreteTopology Y]
    (f : X → Y) (hc : Continuous f) (hi : Function.Injective f) : DiscreteTopology X := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  have he : f ⁻¹' {f x} = {x} := by
    ext y
    exact hi.eq_iff
  rw [← he]
  exact (isOpen_discrete _).preimage hc

theorem pointwiseArrayLattice_discrete {Z G : Type*} [Group G]
    [TopologicalSpace G] (A : Subgroup (Z → G)) (Γ : Subgroup G)
    [DiscreteTopology Γ] (N : ℕ) (u : Fin N → Z)
    (hu : Function.Injective (fun a : A => fun i => a.val (u i))) :
    DiscreteTopology (pointwiseArrayLattice A Γ) := by
  let f : pointwiseArrayLattice A Γ → (Fin N → Γ) := fun a i =>
    ⟨a.val.val (u i), (pointwiseArrayLattice_mem A Γ a.val).mp a.property (u i)⟩
  apply discreteTopology_of_continuous_injective f
  · apply continuous_pi
    intro i
    exact (((continuous_apply (u i)).comp continuous_subtype_val).comp
      continuous_subtype_val).subtype_mk _
  · intro a b hab
    apply Subtype.ext
    apply hu
    funext i
    exact congrArg Subtype.val (congrFun hab i)

end Hindman168
