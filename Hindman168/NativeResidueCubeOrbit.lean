import Hindman168.NativeResidueCubeData
import Hindman168.NativeFiniteProductCoordinateTopology

/-! The actual residue cube quotient embeds in the ORIGINAL vertex cosets.
Every representative maps to (h x_V rho Gamma)_V. -/
namespace Hindman168
open Set
open scoped Manifold ContDiff
universe u
attribute [local instance] nativeFiniteProductTopologicalSpace nativeFiniteProductGroup

theorem native_cube_vertex_difference {G : Type*} [Group G]
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (x y : nativeFiniteProduct G n)
    (V : Finset (Fin d)) :
    nativeCubeVertexHom d n e (x⁻¹*y) V =
      (nativeCubeVertexHom d n e x V)⁻¹ * nativeCubeVertexHom d n e y V := by
  rw [map_mul, map_inv]
  rfl

theorem native_residue_cube_lattice_vertices {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (x : (nativeResidueCubeData D F ρ hρ d n e).G) :
    x ∈ (nativeResidueCubeData D F ρ hρ d n e).Γ ↔
      ∀ V, nativeCubeVertexHom (G := D.G) d n e x.val V ∈ roughConjugateSubgroup D.Γ ρ := by
  change x.val ∈ nativeFiniteProductLattice (roughConjugateSubgroup D.Γ ρ) n ↔ _
  refine (nativeFiniteProductLattice_mem_iff (roughConjugateSubgroup D.Γ ρ) n (x.val : nativeFiniteProduct D.G n)).trans ?_
  constructor
  · exact fun hx V => hx (e.symm V)
  · intro hx k
    have hk := hx (e k)
    simpa only [nativeCubeVertexHom, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.symm_apply_apply] using hk

noncomputable def nativeResidueCubeOrbitMap {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G) :
    (nativeResidueCubeData D F ρ hρ d n e).G ⧸ (nativeResidueCubeData D F ρ hρ d n e).Γ →
      (Finset (Fin d) → D.G ⧸ D.Γ) :=
  Quotient.lift (fun x => fun V =>
    (h * nativeCubeVertexHom (G := D.G) d n e x.val V * ρ : D.G ⧸ D.Γ)) (by
      intro x y hxy
      funext V
      apply QuotientGroup.eq.mpr
      have hm := (native_residue_cube_lattice_vertices D F ρ hρ d n e (x⁻¹*y)).mp
        (QuotientGroup.leftRel_apply.mp hxy) V
      change nativeCubeVertexHom (G := D.G) d n e (x.val⁻¹*y.val) V ∈ _ at hm
      have hm' := (native_cube_vertex_difference d n e (x.val : nativeFiniteProduct D.G n) y.val V) ▸ hm
      have he : (h * nativeCubeVertexHom (G := D.G) d n e x.val V * ρ)⁻¹ *
          (h * nativeCubeVertexHom (G := D.G) d n e y.val V * ρ) =
          ρ⁻¹ * ((nativeCubeVertexHom (G := D.G) d n e x.val V)⁻¹ * nativeCubeVertexHom (G := D.G) d n e y.val V) * ρ := by group
      rw [he]
      exact (roughConjugateSubgroup_mem_iff D.Γ ρ _).mp hm')

theorem native_residue_cube_orbit_map_mk {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G)
    (x : (nativeResidueCubeData D F ρ hρ d n e).G) (V : Finset (Fin d)) :
    nativeResidueCubeOrbitMap D F ρ hρ d n e h (QuotientGroup.mk x) V =
      (h * nativeCubeVertexHom (G := D.G) d n e x.val V * ρ : D.G ⧸ D.Γ) := rfl

theorem native_residue_cube_orbit_map_injective {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G) :
    Function.Injective (nativeResidueCubeOrbitMap D F ρ hρ d n e h) := by
  intro a b
  induction a, b using Quotient.inductionOn₂ with
  | _ x y =>
    intro hxy
    apply QuotientGroup.eq.mpr
    apply (native_residue_cube_lattice_vertices D F ρ hρ d n e (x⁻¹*y)).mpr
    intro V
    have hv := QuotientGroup.eq.mp (congrFun hxy V)
    change (h * nativeCubeVertexHom (G := D.G) d n e x.val V * ρ)⁻¹ *
      (h * nativeCubeVertexHom (G := D.G) d n e y.val V * ρ) ∈ D.Γ at hv
    change nativeCubeVertexHom (G := D.G) d n e (x.val⁻¹*y.val) V ∈ _
    have hm : (nativeCubeVertexHom (G := D.G) d n e x.val V)⁻¹ *
        nativeCubeVertexHom (G := D.G) d n e y.val V ∈ roughConjugateSubgroup D.Γ ρ := by
      apply (roughConjugateSubgroup_mem_iff D.Γ ρ _).mpr
      convert hv using 1
      group
    exact (native_cube_vertex_difference d n e (x.val : nativeFiniteProduct D.G n) y.val V).symm ▸ hm

theorem native_residue_cube_orbit_map_continuous {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G) :
    Continuous (nativeResidueCubeOrbitMap D F ρ hρ d n e h) := by
  apply continuous_quot_lift
  apply continuous_pi
  intro V
  exact QuotientGroup.continuous_mk.comp
    ((continuous_const.mul ((nativeFiniteProductCoordinate_continuous n (e.symm V)).comp continuous_subtype_val)).mul continuous_const)

theorem native_residue_cube_orbit_range_compact {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G) :
    IsCompact (range (nativeResidueCubeOrbitMap D F ρ hρ d n e h)) :=
  isCompact_range (native_residue_cube_orbit_map_continuous D F ρ hρ d n e h)

end Hindman168
