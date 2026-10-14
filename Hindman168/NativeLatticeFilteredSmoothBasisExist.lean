import Hindman168.NativeLatticeOrderedSmoothBasis
import Hindman168.NativeLieLowerCentralModel

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

def NativeLatticeFilteredSmoothBasisExist (Γ : Subgroup G) : Prop :=
  ∃ m : ℕ, m = Module.finrank ℝ E ∧ ∃ w : Fin m → E,
    (∀ i, nativeLieExponential (I := I) (G := G) (w i) ∈ Γ ∧
      w i ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) ∧
    LinearIndependent ℝ w ∧
    Function.Bijective (nativeOrderedExponentialCoordinates (I := I) (G := G) w) ∧
    (∀ x, nativeOrderedExponentialCoordinates (I := I) (G := G) w x ∈ Γ ↔
      ∀ i, ∃ n : ℤ, x i = (n : ℝ)) ∧
    NativeOrderedCoordinateSmoothInverse (I := I) (G := G) w ∧
    ∃ t : ℕ → ℕ, ∀ k,
      t k ≤ m ∧
      (∀ i, w i ∈ nativeLieLowerCentralModel (I := I) (G := G) k ↔ t k ≤ i.val) ∧
      Submodule.span ℝ (w '' {i | t k ≤ i.val}) = nativeLieLowerCentralModel (I := I) (G := G) k

theorem native_lattice_filtered_smooth_basis_subsingleton (Γ : Subgroup G) [Subsingleton G] :
    NativeLatticeFilteredSmoothBasisExist (E := E) (I := I) Γ := by
  letI : Subsingleton E := ⟨fun x y => nativeLieExponential_injective (I := I) (G := G)
    (Subsingleton.elim _ _)⟩
  obtain ⟨m, hm, w, hw, hli, hbij, hlat, hinv⟩ :=
    native_lattice_ordered_smooth_basis_subsingleton (I := I) Γ
  have hm0 : m = 0 := hm.trans (Module.finrank_zero_of_subsingleton (R := ℝ) (M := E))
  have hzero : 0 = Module.finrank ℝ E := hm0.symm.trans hm
  clear hm
  subst m
  refine ⟨0, hzero, w, hw, hli, hbij, hlat, hinv, fun _ => 0, ?_⟩
  intro k
  refine ⟨le_rfl, fun i => Fin.elim0 i, ?_⟩
  have he : w '' {i | 0 ≤ i.val} = (∅ : Set E) := by
    ext v
    constructor
    · rintro ⟨i, _, _⟩
      exact Fin.elim0 i
    · exact False.elim
  rw [he, Submodule.span_empty]
  exact Subsingleton.elim _ _

end Hindman168
