import Hindman168.NativeCubeAmbientRationality
import Hindman168.NativeCubeInclusionRationality
import Hindman168.RationalRealSpanTransport

/-! The FULL paper cube filtration on the actual native cube subgroup.
Both initial layers are internal top; every layer is rational for the
actual internal lattice and the original degree bound is retained. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] nativeFiniteProductTopologicalSpace nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three

attribute [local instance] pointwiseLieRing pointwiseLieAlgebra

attribute [local instance] nativeFiniteProductRationalModule


attribute [local instance] nativeFiniteProduct_topologicalGroup

attribute [local instance] nativeFiniteProductModelTopology

noncomputable def nativeCubeInternalLayer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (i : ℕ) :
    Submodule ℝ (nativeRationalCubeData D F d n e).E :=
  (nativeCubeAmbientLayer D F d n e i).comap (nativeRationalCubeModelInclusion D F d n e).toLinearMap

theorem native_cube_internal_antitone {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) : Antitone (nativeCubeInternalLayer D F d n e) := by
  intro i j hij
  exact Submodule.comap_mono (native_cube_ambient_antitone D F d n e hij)

theorem native_cube_internal_zero {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) : nativeCubeInternalLayer D F d n e 0 = ⊤ := by
  apply top_unique
  intro v _
  change nativeRationalCubeModelInclusion D F d n e v ∈ nativeCubeAmbientLayer D F d n e 0
  exact (native_cube_ambient_zero D F d n e).symm ▸ v.property

theorem native_cube_internal_one {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) : nativeCubeInternalLayer D F d n e 1 = ⊤ := by
  have he := congrArg (fun V => V.comap (nativeRationalCubeModelInclusion D F d n e).toLinearMap)
    (native_cube_ambient_initial D F d n e)
  exact he.symm.trans (native_cube_internal_zero D F d n e)

theorem native_cube_internal_bracket {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (i j : ℕ)
    (v w : (nativeRationalCubeData D F d n e).E)
    (hv : v ∈ nativeCubeInternalLayer D F d n e i) (hw : w ∈ nativeCubeInternalLayer D F d n e j) :
    nativeLieAdjointDifferential (I := (nativeRationalCubeData D F d n e).I)
      (G := (nativeRationalCubeData D F d n e).G) v w ∈ nativeCubeInternalLayer D F d n e (i+j) := by
  change nativeRationalCubeModelInclusion D F d n e
    (nativeLieAdjointDifferential (I := (nativeRationalCubeData D F d n e).I)
      (G := (nativeRationalCubeData D F d n e).G) v w) ∈ nativeCubeAmbientLayer D F d n e (i+j)
  rw [native_rational_cube_inclusion_adjoint]
  exact native_cube_ambient_bracket D F d n e i j _ _ hv hw

theorem native_cube_internal_terminal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) : nativeCubeInternalLayer D F d n e (ℓ+1) = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  have hm : nativeRationalCubeModelInclusion D F d n e v ∈ nativeCubeAmbientLayer D F d n e (ℓ+1) := hv
  have hz : nativeRationalCubeModelInclusion D F d n e v = 0 := by
    rw [native_cube_ambient_terminal,Submodule.mem_bot] at hm
    exact hm
  exact Subtype.ext hz

theorem native_cube_internal_rational {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (i : ℕ) :
    nativeLatticeRationalSubspace (E := (nativeRationalCubeData D F d n e).E)
      (I := (nativeRationalCubeData D F d n e).I) (nativeRationalCubeData D F d n e).Γ
      (nativeCubeInternalLayer D F d n e i) := by
  letI := nativeFiniteProductSimplyConnected (I := D.I) (G := D.G) n
  let L := (nativeRationalCubeModelInclusion D F d n e).toLinearMap
  have hRange : nativeCubeAmbientLayer D F d n e i ≤ L.range := by
    intro v hv
    have hv0 := native_cube_ambient_antitone D F d n e (Nat.zero_le i) hv
    have hm := (native_cube_ambient_zero D F d n e) ▸ hv0
    exact ⟨⟨v,hm⟩,rfl⟩
  exact rational_real_span_comap L Subtype.val_injective (nativeCubeAmbientLayer D F d n e i) hRange
    (nativeSubgroupRationalLogSpan (E := (nativeRationalCubeData D F d n e).E)
      (I := (nativeRationalCubeData D F d n e).I) (nativeRationalCubeData D F d n e).Γ)
    (nativeSubgroupRationalLogSpan (E := nativeFiniteProduct D.E n)
      (I := nativeFiniteProductCorners D.I n) (nativeFiniteProductLattice D.Γ n))
    (native_cube_inclusion_rational_iff D F d n e) (native_cube_ambient_layer_rational D F d n e i)

noncomputable def nativeCubeRationalLieFiltration {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    NativeRationalLieFiltration (nativeRationalCubeData D F d n e) ℓ where
  layer := nativeCubeInternalLayer D F d n e
  antitone := native_cube_internal_antitone D F d n e
  zero := native_cube_internal_zero D F d n e
  one := native_cube_internal_one D F d n e
  bracket := native_cube_internal_bracket D F d n e
  rational := native_cube_internal_rational D F d n e
  terminal := native_cube_internal_terminal D F d n e

end Hindman168
