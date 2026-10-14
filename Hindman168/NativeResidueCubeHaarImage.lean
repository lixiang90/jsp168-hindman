import Hindman168.NativeResidueCubeOrbit
import Hindman168.NativeNilmanifoldQuotientProbability

/-! Actual normalized invariant probability pushed to ORIGINAL cube cosets.
No empirical equidistribution or prescribed Haar limit is assumed. -/
namespace Hindman168
open Set MeasureTheory
open scoped Manifold ContDiff
universe u

noncomputable def nativeResidueCubeHaarImage {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G) :
    letI : MeasurableSpace D.G := borel D.G
    Measure (Finset (Fin d) → D.G ⧸ D.Γ) := by
  letI : MeasurableSpace D.G := borel D.G
  let A := nativeResidueCubeData D F ρ hρ d n e
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  exact Measure.map (nativeResidueCubeOrbitMap D F ρ hρ d n e h)
    (nativeNilmanifoldQuotientProbability A)

theorem native_residue_cube_haar_isProbability {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G) :
    letI : MeasurableSpace D.G := borel D.G
    IsProbabilityMeasure (nativeResidueCubeHaarImage D F ρ hρ d n e h) := by
  letI : MeasurableSpace D.G := borel D.G
  let A := nativeResidueCubeData D F ρ hρ d n e
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI : PolishSpace D.G := native_nilmanifold_group_polish D
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_coset_borel D
  letI : BorelSpace (A.G ⧸ A.Γ) := native_nilmanifold_coset_borel A
  letI := native_nilmanifold_quotient_probability_isProbability A
  exact Measure.isProbabilityMeasure_map
    (native_residue_cube_orbit_map_continuous D F ρ hρ d n e h).measurable.aemeasurable

theorem native_residue_cube_haar_concentrated {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G) :
    letI : MeasurableSpace D.G := borel D.G
    ∀ᵐ z ∂nativeResidueCubeHaarImage D F ρ hρ d n e h,
      z ∈ range (nativeResidueCubeOrbitMap D F ρ hρ d n e h) := by
  letI : MeasurableSpace D.G := borel D.G
  let A := nativeResidueCubeData D F ρ hρ d n e
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI : PolishSpace D.G := native_nilmanifold_group_polish D
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_coset_borel D
  letI : BorelSpace (A.G ⧸ A.Γ) := native_nilmanifold_coset_borel A
  letI : IsClosed (D.Γ : Set D.G) := Subgroup.isClosed_of_discrete
  exact ae_map_mem_range _
    (native_residue_cube_orbit_range_compact D F ρ hρ d n e h).isClosed.measurableSet _

end Hindman168
