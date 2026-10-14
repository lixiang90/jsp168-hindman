import Hindman168.RationalSubspaceSpanIntersection

/-! Real-spanning rational intersections transport through actual linear
inclusions and projections. The generators, not an abstract coordinate
lattice, are retained. -/

namespace Hindman168
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [Module ℚ E]
  [AddCommGroup F] [Module ℝ F] [Module ℚ F]

theorem rational_real_span_comap (L : E →ₗ[ℝ] F) (hL : Function.Injective L)
    (V : Submodule ℝ F) (hVrange : V ≤ LinearMap.range L)
    (W : Submodule ℚ E) (W' : Submodule ℚ F)
    (hW : ∀ v, v ∈ W ↔ L v ∈ W')
    (hV : Submodule.span ℝ ((V.restrictScalars ℚ ⊓ W' : Submodule ℚ F) : Set F) = V) :
    Submodule.span ℝ (((V.comap L).restrictScalars ℚ ⊓ W : Submodule ℚ E) : Set E) = V.comap L := by
  have hImage : L '' (((V.comap L).restrictScalars ℚ ⊓ W : Submodule ℚ E) : Set E) =
      ((V.restrictScalars ℚ ⊓ W' : Submodule ℚ F) : Set F) := by
    ext v
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨ha.1,(hW a).mp ha.2⟩
    · intro hv
      obtain ⟨a,rfl⟩ := hVrange hv.1
      exact ⟨a,⟨hv.1,(hW a).mpr hv.2⟩,rfl⟩
  have hMap : (V.comap L).map L = V := by
    ext v
    constructor
    · rintro ⟨a,ha,rfl⟩; exact ha
    · intro hv
      obtain ⟨a,rfl⟩ := hVrange hv
      exact ⟨a,hv,rfl⟩
  apply Submodule.map_injective_of_injective hL
  rw [Submodule.map_span,hImage,hV,hMap]

theorem rational_real_span_map (L : E →ₗ[ℝ] F)
    (V : Submodule ℝ E) (W : Submodule ℚ E) (W' : Submodule ℚ F)
    (hW : ∀ v, v ∈ W → L v ∈ W')
    (hV : Submodule.span ℝ ((V.restrictScalars ℚ ⊓ W : Submodule ℚ E) : Set E) = V) :
    Submodule.span ℝ (((V.map L).restrictScalars ℚ ⊓ W' : Submodule ℚ F) : Set F) = V.map L := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun _ hv => hv.1)
  · conv_lhs => rw [← hV,Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro v ⟨a,ha,rfl⟩
    apply Submodule.subset_span
    exact ⟨Submodule.mem_map_of_mem ha.1,hW a ha.2⟩

end Hindman168
