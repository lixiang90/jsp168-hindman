import Hindman168.NativeRationalCharacterKernel

/-! A genuine original lattice pivot reduces the character coordinate
to a unit segment, with a residual in the smaller original kernel.
No normality of the specified lattice or discrete character image is used. -/

namespace Hindman168
open Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeCharacter_lattice_reduction
    (Γ : Subgroup G) (S T : LieSubalgebra ℝ (GroupLieAlgebra I G)) (F : E →ₗ[ℝ] ℝ)
    (hker : ∀ g : G, g ∈ nativeLieSubalgebraSubgroup (E := E) T ↔
      g ∈ nativeLieSubalgebraSubgroup (E := E) S ∧
        nativeLieLogarithmCharacter (I := I) (G := G) F g = 0)
    (hmul : ∀ g ∈ nativeLieSubalgebraSubgroup (E := E) S,
      ∀ h ∈ nativeLieSubalgebraSubgroup (E := E) S,
        nativeLieLogarithmCharacter (I := I) (G := G) F (g * h) =
          nativeLieLogarithmCharacter (I := I) (G := G) F g +
            nativeLieLogarithmCharacter (I := I) (G := G) F h)
    (γ : G) (hγ : γ ∈ Γ) (hγS : γ ∈ nativeLieSubalgebraSubgroup (E := E) S)
    (hγF : nativeLieLogarithmCharacter (I := I) (G := G) F γ ≠ 0)
    (g : G) (hg : g ∈ nativeLieSubalgebraSubgroup (E := E) S) :
    ∃ r ∈ Icc (0 : ℝ) 1, ∃ u ∈ nativeLieSubalgebraSubgroup (E := E) T,
      ∃ z : ℤ, γ ^ z ∈ Γ ∧
        g = nativeLieExponential (I := I) (G := G)
          (r • nativeLieGlobalLogarithm (E := E) (I := I) (G := G) γ) * u * γ ^ z := by
  let χ := nativeLieLogarithmCharacter (I := I) (G := G) F
  let v : E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G) γ
  let t : ℝ := χ g / χ γ
  let z : ℤ := Int.floor t
  let r : ℝ := t - (z : ℝ)
  let a : G := nativeLieExponential (I := I) (G := G) (r • v)
  let c : G := nativeLieExponential (I := I) (G := G) (-(r • v))
  let b : G := nativeLieExponential (I := I) (G := G) (-((z : ℝ) • v))
  let u : G := c * g * b
  have hv : v ∈ nativeLieSubalgebraModel S :=
    (nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff (E := E) S γ).mp hγS
  have hcS : c ∈ nativeLieSubalgebraSubgroup (E := E) S :=
    ⟨-(r • v), (nativeLieSubalgebraModel S).neg_mem
      ((nativeLieSubalgebraModel S).smul_mem r hv), rfl⟩
  have hbS : b ∈ nativeLieSubalgebraSubgroup (E := E) S :=
    ⟨-((z : ℝ) • v), (nativeLieSubalgebraModel S).neg_mem
      ((nativeLieSubalgebraModel S).smul_mem (z : ℝ) hv), rfl⟩
  have huS : u ∈ nativeLieSubalgebraSubgroup (E := E) S :=
    (nativeLieSubalgebraSubgroup (E := E) S).mul_mem
      ((nativeLieSubalgebraSubgroup (E := E) S).mul_mem hcS hg) hbS
  have hcχ : χ c = -(r * χ γ) := by
    change nativeLieLogarithmCharacter (I := I) (G := G) F
      (nativeLieExponential (I := I) (G := G) (-(r • v))) = _
    rw [nativeLieLogarithmCharacter_exponential, map_neg, map_smul]
    rfl
  have hbχ : χ b = -((z : ℝ) * χ γ) := by
    change nativeLieLogarithmCharacter (I := I) (G := G) F
      (nativeLieExponential (I := I) (G := G) (-((z : ℝ) • v))) = _
    rw [nativeLieLogarithmCharacter_exponential, map_neg, map_smul]
    rfl
  have huχ : χ u = 0 := by
    change χ (c * g * b) = 0
    rw [hmul (c * g) ((nativeLieSubalgebraSubgroup (E := E) S).mul_mem hcS hg) b hbS,
      hmul c hcS g hg, hcχ, hbχ]
    have ht : t * χ γ = χ g := div_mul_cancel₀ _ hγF
    dsimp only [r]
    nlinarith
  have huT : u ∈ nativeLieSubalgebraSubgroup (E := E) T := (hker u).mpr ⟨huS, huχ⟩
  have hr : r ∈ Icc (0 : ℝ) 1 := by
    refine ⟨sub_nonneg.mpr (Int.floor_le t), ?_⟩
    have ht := Int.lt_floor_add_one t
    change t - (Int.floor t : ℝ) ≤ 1
    linarith
  have hc : c = a⁻¹ := nativeLieExponential_neg (I := I) (G := G) (r • v)
  have hb : b = (γ ^ z)⁻¹ := by
    calc
      b = (nativeLieExponential (I := I) (G := G) ((z : ℝ) • v))⁻¹ :=
        nativeLieExponential_neg (I := I) (G := G) ((z : ℝ) • v)
      _ = (γ ^ z)⁻¹ := congrArg Inv.inv
        ((nativeLieExponential_int_smul (I := I) (G := G) v z).trans
          (congrArg (fun h : G => h ^ z) (nativeLieExponential_globalLogarithm (I := I) γ)))
  refine ⟨r, hr, u, huT, z, Γ.zpow_mem hγ z, ?_⟩
  change g = a * u * γ ^ z
  dsimp only [u]
  rw [hc, hb]
  group

end Hindman168
