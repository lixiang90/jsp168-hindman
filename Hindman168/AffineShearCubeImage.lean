import Hindman168.NilUpperFaceGroup

/-! Full vertexwise marginal cubes commute exactly with group images.
This result concerns one fixed group homomorphism at EVERY vertex; it does
not identify a mixed-vertex binary-slot projection with a marginal cube. -/
namespace Hindman168

noncomputable def affineShearVertexMap {G K : Type*} [Group G] [Group K]
    (d : ℕ) (p : G →* K) : (Finset (Fin d) → G) →* (Finset (Fin d) → K) where
  toFun z V := p (z V)
  map_one' := by funext V; exact p.map_one
  map_mul' z w := by funext V; exact p.map_mul (z V) (w V)

 theorem affineShearVertexMap_face {G K : Type*} [Group G] [Group K]
    (d : ℕ) (p : G →* K) (A : Finset (Fin d)) (g : G) :
    affineShearVertexMap d p (upperFaceArray A g) = upperFaceArray A (p g) := by
  classical
  funext V
  by_cases h : A ⊆ V <;> simp [affineShearVertexMap, upperFaceArray, h]

 theorem affineShear_cube_image {G K : Type*} [Group G] [Group K]
    (F : ℕ → Subgroup G) (d : ℕ) (p : G →* K) :
    (upperFaceCubeGroup F d).map (affineShearVertexMap d p) =
      upperFaceCubeGroup (fun i => (F i).map p) d := by
  unfold upperFaceCubeGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨a, ⟨A, g, hg, rfl⟩, rfl⟩
    exact ⟨A, p g, ⟨g, hg, rfl⟩, affineShearVertexMap_face d p A g⟩
  · rintro ⟨A, g, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨upperFaceArray A a, ⟨A, a, ha, rfl⟩, affineShearVertexMap_face d p A a⟩

end Hindman168
