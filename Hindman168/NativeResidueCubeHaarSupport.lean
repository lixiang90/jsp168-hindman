import Hindman168.NativeResidueCubeHaarImage
import Hindman168.NativeNilmanifoldProbabilityFullSupport

/-! The actual cube orbit is a closed embedded compact quotient, and its
Haar image has exactly that orbit as support, via positivity on opens. -/
namespace Hindman168
open Set MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_residue_cube_orbit_closedEmbedding {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G) :
    Topology.IsClosedEmbedding (nativeResidueCubeOrbitMap D F ρ hρ d n e h) := by
  letI : IsClosed (D.Γ : Set D.G) := Subgroup.isClosed_of_discrete
  exact (native_residue_cube_orbit_map_continuous D F ρ hρ d n e h).isClosedEmbedding
    (native_residue_cube_orbit_map_injective D F ρ hρ d n e h)

theorem native_residue_cube_haar_open_pos_iff {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G) :
    letI : MeasurableSpace D.G := borel D.G
    ∀ U : Set (Finset (Fin d) → D.G ⧸ D.Γ), IsOpen U →
      (0 < nativeResidueCubeHaarImage D F ρ hρ d n e h U ↔
        (U ∩ range (nativeResidueCubeOrbitMap D F ρ hρ d n e h)).Nonempty) := by
  letI : MeasurableSpace D.G := borel D.G
  let A := nativeResidueCubeData D F ρ hρ d n e
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI : PolishSpace D.G := native_nilmanifold_group_polish D
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_coset_borel D
  letI : BorelSpace (A.G ⧸ A.Γ) := native_nilmanifold_coset_borel A
  letI := native_nilmanifold_quotient_probability_fullSupport A
  intro U hU
  have hc := native_residue_cube_orbit_map_continuous D F ρ hρ d n e h
  change 0 < Measure.map _ (nativeNilmanifoldQuotientProbability A) U ↔ _
  rw [Measure.map_apply hc.measurable hU.measurableSet,
    (hU.preimage hc).measure_pos_iff (μ := nativeNilmanifoldQuotientProbability A)]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨_,hx,x,rfl⟩
  · rintro ⟨z,hz,x,rfl⟩
    exact ⟨x,hz⟩

end Hindman168
