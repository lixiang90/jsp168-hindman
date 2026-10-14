import Hindman168.RoughNativeFixedKernel

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def roughNativeKernelFactor (V : E) (a m : ℝ) (g : G) : G :=
  nativeLieExponential (I := I) (G := G) (-(a • V)) * g *
    nativeLieExponential (I := I) (G := G) (-(m • V))

theorem rough_native_kernel_factor_mem
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (F : E →ₗ[ℝ] ℝ)
    (hF : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0)
    (V : E) (hV : V ∈ nativeLieSubalgebraModel S) (hFV : F V = 1)
    (a m : ℝ) (g : G) (hg : g ∈ nativeLieSubalgebraSubgroup (E := E) S)
    (hchi : nativeLieLogarithmCharacter (I := I) (G := G) F g = a + m) :
    roughNativeKernelFactor (I := I) V a m g ∈
      nativeLieSubalgebraSubgroup (E := E) (nativeLieCharacterKernel S F hF) := by
  let L := nativeLieSubalgebraSubgroup (E := E) S
  have ha : nativeLieExponential (I := I) (G := G) (-(a • V)) ∈ L :=
    ⟨-(a • V), (nativeLieSubalgebraModel S).neg_mem ((nativeLieSubalgebraModel S).smul_mem a hV), rfl⟩
  have hm : nativeLieExponential (I := I) (G := G) (-(m • V)) ∈ L :=
    ⟨-(m • V), (nativeLieSubalgebraModel S).neg_mem ((nativeLieSubalgebraModel S).smul_mem m hV), rfl⟩
  apply (nativeLieCharacterKernel_subgroup_mem_iff S F hF _).mpr
  refine ⟨L.mul_mem (L.mul_mem ha hg) hm, ?_⟩
  unfold roughNativeKernelFactor
  rw [nativeLieSubalgebra_character_mul S F hF (L.mul_mem ha hg) hm,
    nativeLieSubalgebra_character_mul S F hF ha hg,
    nativeLieLogarithmCharacter_exponential, nativeLieLogarithmCharacter_exponential,
    map_neg, map_neg, map_smul, map_smul, hFV, hchi]
  simp only [smul_eq_mul, mul_one]
  ring

omit [Module ℚ E] [Group.IsNilpotent G] [FiniteDimensional ℝ E]
  [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem rough_native_kernel_factorization (V : E) (a m : ℝ) (g : G) :
    g = nativeLieExponential (I := I) (G := G) (a • V) *
      roughNativeKernelFactor (I := I) V a m g *
        nativeLieExponential (I := I) (G := G) (m • V) := by
  let A : G := nativeLieExponential (I := I) (G := G) (a • V)
  let B : G := nativeLieExponential (I := I) (G := G) (m • V)
  have ha : nativeLieExponential (I := I) (G := G) (-(a • V)) = A⁻¹ :=
    nativeLieExponential_neg (I := I) (G := G) (a • V)
  have hm : nativeLieExponential (I := I) (G := G) (-(m • V)) = B⁻¹ :=
    nativeLieExponential_neg (I := I) (G := G) (m • V)
  have hQ : roughNativeKernelFactor (I := I) V a m g = A⁻¹ * g * B⁻¹ :=
    congrArg₂ (fun x y : G => x * g * y) ha hm
  change g = A * roughNativeKernelFactor (I := I) V a m g * B
  rw [hQ]
  group

end Hindman168
