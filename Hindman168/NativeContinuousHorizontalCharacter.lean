import Hindman168.NativeContinuousCharacterLinearization

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_continuous_character_linearization_horizontal (χ : G → ℝ)
    (hmul : ∀ g h, χ (g*h) = χ g + χ h) (f : E →L[ℝ] ℝ)
    (hrep : ∀ g, χ g = f (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g)) :
    nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ f.toLinearMap.ker := by
  intro v hv
  have hg : nativeLieExponential (I := I) (G := G) v ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
    rw [nativeGroupLowerCentralSeries_eq_exponential (E := E) (I := I)]
    exact ⟨v, hv, rfl⟩
  have hz := native_additive_character_commutator χ hmul _ hg
  rw [hrep, nativeLieGlobalLogarithm_exponential] at hz
  exact hz

theorem native_continuous_horizontal_character_representation (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (χ : G → ℝ) (hcont : Continuous χ)
    (hmul : ∀ g h, χ (g*h) = χ g + χ h) (hne : χ ≠ 0)
    (hint : ∀ γ ∈ Γ, ∃ m : ℤ, χ γ = (m : ℝ)) :
    ∃! f : E →L[ℝ] ℝ, RoughNativeHorizontalFunctional (E := E) (I := I) Γ f.toLinearMap ∧
      ∀ g, χ g = f (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) := by
  obtain ⟨f, hf, huniq⟩ := native_continuous_character_linearization (I := I) Γ χ hcont hmul
  refine ⟨f, ⟨⟨?_, native_continuous_character_linearization_horizontal (I := I) χ hmul f hf, ?_⟩, hf⟩,
    fun f' hf' => huniq f' hf'.2⟩
  · intro hz
    apply hne
    funext g
    change χ g = 0
    rw [hf]
    exact congrArg (fun l : E →ₗ[ℝ] ℝ => l
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g)) hz
  · intro γ hγ
    obtain ⟨m, hm⟩ := hint γ hγ
    exact ⟨m, (hf γ).symm.trans hm⟩

end Hindman168
