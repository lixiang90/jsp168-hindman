import Hindman168.NativeSmoothBasisCharacterIntegrality
import Hindman168.NativeLatticeOrderedSmoothBasisCoordinates
import Hindman168.RoughNativeHorizontalCharacterGrid

/-! Integer coefficient vectors on the fixed smooth original lattice basis
give all lattice-integral horizontal differentials. Finite equations in the
actual rational bracket structure constants test horizontality exactly. -/

namespace Hindman168
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeSmoothBasisIntegerFunctional (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (a : Fin (Module.finrank ℝ E) → ℤ) : E →ₗ[ℝ] ℝ :=
  (nativeLatticeOrderedSmoothRealBasis (I := I) Γ).constr ℝ (fun i => (a i : ℝ))

theorem native_smooth_basis_integer_functional_basis (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (a : Fin (Module.finrank ℝ E) → ℤ) (i : Fin (Module.finrank ℝ E)) :
    nativeSmoothBasisIntegerFunctional (I := I) Γ a
      (nativeLatticeOrderedSmoothRealBasis (I := I) Γ i) = (a i : ℝ) :=
  (nativeLatticeOrderedSmoothRealBasis (I := I) Γ).constr_basis ℝ _ i

theorem native_smooth_basis_integer_functional_injective (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Function.Injective (nativeSmoothBasisIntegerFunctional (I := I) Γ) := by
  intro a c h
  funext i
  apply Int.cast_injective (α := ℝ)
  have hi := congrArg (fun f : E →ₗ[ℝ] ℝ => f (nativeLatticeOrderedSmoothRealBasis (I := I) Γ i)) h
  simpa only [native_smooth_basis_integer_functional_basis] using hi

theorem native_smooth_basis_integer_functional_zero (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    nativeSmoothBasisIntegerFunctional (I := I) Γ 0 = 0 := by
  apply (nativeLatticeOrderedSmoothRealBasis (I := I) Γ).ext
  intro i
  simp only [native_smooth_basis_integer_functional_basis, Pi.zero_apply,
    Int.cast_zero, LinearMap.zero_apply]

theorem native_smooth_basis_integer_functional_zero_iff (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (a : Fin (Module.finrank ℝ E) → ℤ) :
    nativeSmoothBasisIntegerFunctional (I := I) Γ a = 0 ↔ a = 0 := by
  rw [← native_smooth_basis_integer_functional_zero (I := I) Γ]
  exact (native_smooth_basis_integer_functional_injective (I := I) Γ).eq_iff

theorem native_smooth_basis_horizontal_finite_test (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (f : E →ₗ[ℝ] ℝ) :
    nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ f.ker ↔
      ∀ i j, f (nativeLieAdjointDifferential (I := I) (G := G)
        (nativeLatticeOrderedSmoothRealBasis (I := I) Γ i)
        (nativeLatticeOrderedSmoothRealBasis (I := I) Γ j)) = 0 := by
  let b := nativeLatticeOrderedSmoothRealBasis (I := I) Γ
  let B := nativeLieAdjointDifferential (I := I) (G := G)
  constructor
  · intro hf i j
    rw [← nativeLieAdjointGenerator_eq_differential]
    exact hf (nativeLieAdjointGenerator_mem_lowerCentral_next (I := I) (G := G) (b i)
      (j := 0) (nativeLieLowerCentralModel_zero (I := I) (G := G) ▸ trivial))
  · intro h
    apply nativeLieFunctional_lowerCentral_le_kernel
    have hleft : ∀ j, f.comp (B.flip (b j)).toLinearMap = 0 := by
      intro j
      apply b.ext
      intro i
      change f (B (b i) (b j)) = 0
      exact h i j
    intro x y
    have hright : f.comp (B x).toLinearMap = 0 := by
      apply b.ext
      intro j
      change f (B x (b j)) = 0
      exact congrArg (fun L : E →ₗ[ℝ] ℝ => L x) (hleft j)
    exact congrArg (fun L : E →ₗ[ℝ] ℝ => L y) hright

theorem native_smooth_basis_integer_horizontal_equations (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (a : Fin (Module.finrank ℝ E) → ℤ) :
    nativeLieLowerCentralModel (I := I) (G := G) 1 ≤
      (nativeSmoothBasisIntegerFunctional (I := I) Γ a).ker ↔
    ∀ i j, ∑ k, (nativeLatticeOrderedSmoothRealBasis (I := I) Γ).equivFun
      (nativeLieAdjointDifferential (I := I) (G := G)
        (nativeLatticeOrderedSmoothRealBasis (I := I) Γ i)
        (nativeLatticeOrderedSmoothRealBasis (I := I) Γ j)) k * (a k : ℝ) = 0 := by
  rw [native_smooth_basis_horizontal_finite_test Γ]
  simp only [nativeSmoothBasisIntegerFunctional, Module.Basis.constr_apply_fintype, smul_eq_mul]

theorem native_smooth_basis_integer_functional_horizontal_iff (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (a : Fin (Module.finrank ℝ E) → ℤ) :
    RoughNativeHorizontalFunctional (E := E) (I := I) Γ
      (nativeSmoothBasisIntegerFunctional (I := I) Γ a) ↔
      a ≠ 0 ∧ nativeLieLowerCentralModel (I := I) (G := G) 1 ≤
        (nativeSmoothBasisIntegerFunctional (I := I) Γ a).ker := by
  constructor
  · intro h
    exact ⟨fun ha => h.1 (by rw [ha, native_smooth_basis_integer_functional_zero (I := I)]), h.2.1⟩
  · rintro ⟨ha, hcomm⟩
    refine ⟨fun hf => ha ((native_smooth_basis_integer_functional_zero_iff (I := I) Γ a).mp hf), hcomm, ?_⟩
    exact (native_smooth_basis_character_integral_iff Γ _ hcomm).mpr
      (fun i => ⟨a i, native_smooth_basis_integer_functional_basis Γ a i⟩)

theorem native_smooth_basis_horizontal_integer_representation (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (f : E →ₗ[ℝ] ℝ)
    (hf : RoughNativeHorizontalFunctional (E := E) (I := I) Γ f) :
    ∃! a : Fin (Module.finrank ℝ E) → ℤ,
      nativeSmoothBasisIntegerFunctional (I := I) Γ a = f := by
  have hint := (native_smooth_basis_character_integral_iff Γ f hf.2.1).mp hf.2.2
  classical
  choose a ha using hint
  have he : nativeSmoothBasisIntegerFunctional (I := I) Γ a = f := by
    apply (nativeLatticeOrderedSmoothRealBasis (I := I) Γ).ext
    intro i
    exact (native_smooth_basis_integer_functional_basis Γ a i).trans (ha i).symm
  refine ⟨a, he, ?_⟩
  intro c hc
  exact native_smooth_basis_integer_functional_injective Γ (hc.trans he.symm)

end Hindman168
