import Hindman168.NativeResidueCubeHaarSupport
import Hindman168.ClosedSupportMeasureSymmetry

/-! Actual projected cube Haar images have exactly the projected compact orbit
as full support. A proved projected measure symmetry therefore preserves that
orbit SETWISE, which is the input required by the marginal face-lift argument. -/
namespace Hindman168
open Set MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_projected_cube_haar_open_pos_iff {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G)
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (π : (Finset (Fin d) → D.G ⧸ D.Γ) → Y) (hπ : Continuous π) :
    letI : MeasurableSpace D.G := borel D.G
    ∀ U : Set Y, IsOpen U →
      (0 < Measure.map π (nativeResidueCubeHaarImage D F ρ hρ d n e h) U ↔
        (U ∩ range (π ∘ nativeResidueCubeOrbitMap D F ρ hρ d n e h)).Nonempty) := by
  letI : MeasurableSpace D.G := borel D.G
  letI : PolishSpace D.G := native_nilmanifold_group_polish D
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_coset_borel D
  intro U hU
  rw [Measure.map_apply hπ.measurable hU.measurableSet,
    native_residue_cube_haar_open_pos_iff D F ρ hρ d n e h _ (hU.preimage hπ)]
  constructor
  · rintro ⟨z,hz,x,rfl⟩
    exact ⟨_,hz,x,rfl⟩
  · rintro ⟨y,hy,x,rfl⟩
    exact ⟨_,hy,x,rfl⟩

theorem native_projected_cube_symmetry_preserves_coset {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G)
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    (π : (Finset (Fin d) → D.G ⧸ D.Γ) → Y) (hπ : Continuous π) (T : Y ≃ₜ Y) :
    letI : MeasurableSpace D.G := borel D.G
    Measure.map T (Measure.map π (nativeResidueCubeHaarImage D F ρ hρ d n e h)) =
      Measure.map π (nativeResidueCubeHaarImage D F ρ hρ d n e h) →
    T '' range (π ∘ nativeResidueCubeOrbitMap D F ρ hρ d n e h) =
      range (π ∘ nativeResidueCubeOrbitMap D F ρ hρ d n e h) := by
  letI : MeasurableSpace D.G := borel D.G
  intro hinv
  have hclosed : IsClosed (range (π ∘ nativeResidueCubeOrbitMap D F ρ hρ d n e h)) :=
    (isCompact_range (hπ.comp (native_residue_cube_orbit_map_continuous D F ρ hρ d n e h))).isClosed
  exact closed_support_homeomorph_invariant _ _ hclosed
    (native_projected_cube_haar_open_pos_iff D F ρ hρ d n e h π hπ) T hinv

end Hindman168
