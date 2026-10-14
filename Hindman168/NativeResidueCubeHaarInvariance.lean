import Hindman168.NativeResidueCubeHaarImage

/-! Actual cube-group invariance of the Haar image, with the translating
smooth factor conjugating the vertex action in the original group. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] nativeFiniteProductGroup nativeFiniteProductTopologicalSpace

noncomputable def nativeResidueCubeVertexAction {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G)
    (y : (nativeResidueCubeData D F ρ hρ d n e).G) :
    (Finset (Fin d) → D.G ⧸ D.Γ) → (Finset (Fin d) → D.G ⧸ D.Γ) :=
  fun z V => (h * nativeCubeVertexHom (G := D.G) d n e y.val V * h⁻¹) • z V

theorem native_residue_cube_vertex_action_continuous {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G)
    (y : (nativeResidueCubeData D F ρ hρ d n e).G) :
    Continuous (nativeResidueCubeVertexAction D F ρ hρ d n e h y) := by
  apply continuous_pi
  intro V
  exact (continuous_const_smul (h * nativeCubeVertexHom (G := D.G) d n e y.val V * h⁻¹)).comp
    (continuous_apply V)

theorem native_residue_cube_orbit_equivariant {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G)
    (y : (nativeResidueCubeData D F ρ hρ d n e).G) :
    nativeResidueCubeVertexAction D F ρ hρ d n e h y ∘ nativeResidueCubeOrbitMap D F ρ hρ d n e h =
      nativeResidueCubeOrbitMap D F ρ hρ d n e h ∘ (fun x => y • x) := by
  funext x V
  obtain ⟨z,rfl⟩ := QuotientGroup.mk_surjective x
  change ((h * nativeCubeVertexHom (G := D.G) d n e y.val V * h⁻¹) *
      (h * nativeCubeVertexHom (G := D.G) d n e z.val V * ρ) : D.G ⧸ D.Γ) =
    (h * nativeCubeVertexHom (G := D.G) d n e (y*z).val V * ρ : D.G ⧸ D.Γ)
  apply congrArg (fun g : D.G => (g : D.G ⧸ D.Γ))
  have hm : nativeCubeVertexHom (G := D.G) d n e (y*z).val V =
      nativeCubeVertexHom (G := D.G) d n e y.val V * nativeCubeVertexHom (G := D.G) d n e z.val V :=
    congrFun (map_mul (nativeCubeVertexHom (G := D.G) d n e)
      (y.val : nativeFiniteProduct D.G n) z.val) V
  calc
    _ = h * (nativeCubeVertexHom (G := D.G) d n e y.val V *
      nativeCubeVertexHom (G := D.G) d n e z.val V) * ρ := by group
    _ = _ := congrArg (fun t : D.G => h*t*ρ) hm.symm

theorem native_residue_cube_haar_invariant {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G)
    (y : (nativeResidueCubeData D F ρ hρ d n e).G) :
    letI : MeasurableSpace D.G := borel D.G
    Measure.map (nativeResidueCubeVertexAction D F ρ hρ d n e h y)
      (nativeResidueCubeHaarImage D F ρ hρ d n e h) = nativeResidueCubeHaarImage D F ρ hρ d n e h := by
  letI : MeasurableSpace D.G := borel D.G
  let A := nativeResidueCubeData D F ρ hρ d n e
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI : PolishSpace D.G := native_nilmanifold_group_polish D
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_coset_borel D
  letI : BorelSpace (A.G ⧸ A.Γ) := native_nilmanifold_coset_borel A
  change Measure.map _ (Measure.map _ (nativeNilmanifoldQuotientProbability A)) =
    Measure.map _ (nativeNilmanifoldQuotientProbability A)
  rw [Measure.map_map
    (native_residue_cube_vertex_action_continuous D F ρ hρ d n e h y).measurable
    (native_residue_cube_orbit_map_continuous D F ρ hρ d n e h).measurable,
    native_residue_cube_orbit_equivariant]
  rw [← Measure.map_map
    (native_residue_cube_orbit_map_continuous D F ρ hρ d n e h).measurable
    (continuous_const_smul y).measurable]
  rw [native_nilmanifold_quotient_probability_translate A y]

end Hindman168
