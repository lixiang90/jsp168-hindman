import Hindman168.AffineShearAdaptedBasis
import Hindman168.AffineShearNativeRestriction
import Hindman168.NativeRationalLayerOrbit
import Hindman168.NativeSmoothHomLieBracket

/-! The original proper level-one subgroup has its own native model.
Its inherited filtration has full initial layer, the original terminal
length and genuine native bracket law.  Adapted weighted coordinates are
therefore constructed inside J, never assumed to span the ambient K'. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def affineShearNativeInitialFiltration {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) (i : ℕ) :
    Submodule ℝ (nativeRationalLayerOrbitData D F 1 ρ hρ).E :=
  (F.layer i).comap (nativeLieSubalgebraModel (nativeRationalSubgroupLayerAlgebra D F 1)).subtype

 theorem affineShear_native_initial_antitone {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    Antitone (affineShearNativeInitialFiltration D F ρ hρ) :=
  fun _ _ hij => Submodule.comap_mono (F.antitone hij)

 theorem affineShear_native_initial_one {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    affineShearNativeInitialFiltration D F ρ hρ 1 = ⊤ := by
  apply top_unique
  intro v _
  exact v.property

 theorem affineShear_native_initial_terminal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    affineShearNativeInitialFiltration D F ρ hρ (ℓ+1) = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  have hv₀ : v.val = 0 := by
    have h : v.val ∈ F.layer (ℓ+1) := hv
    simpa only [F.terminal, Submodule.mem_bot] using h
  change v = 0
  exact Subtype.ext hv₀

 theorem affineShear_native_initial_bracket {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (i j : ℕ) (v w : (nativeRationalLayerOrbitData D F 1 ρ hρ).E)
    (hv : v ∈ affineShearNativeInitialFiltration D F ρ hρ i)
    (hw : w ∈ affineShearNativeInitialFiltration D F ρ hρ j) :
    nativeLieAdjointDifferential (I := (nativeRationalLayerOrbitData D F 1 ρ hρ).I)
      (G := (nativeRationalLayerOrbitData D F 1 ρ hρ).G) v w ∈
        affineShearNativeInitialFiltration D F ρ hρ (i+j) := by
  let L := nativeRationalSubgroupLayerAlgebra D F 1
  letI := nativeLieSubalgebraChartedSpace (E := D.E) L
  letI := nativeLieSubalgebra_lieGroup L
  letI := nativeLieSubalgebra_boundaryless L
  have he := nativeSmoothHom_generator_intertwine
    (I := 𝓘(ℝ, nativeLieSubalgebraModel (E := D.E) L)) (J := D.I)
    (nativeLieSubalgebraSubgroup (E := D.E) L).subtype
    (nativeLieSubalgebra_inclusion_contMDiff (E := D.E) L) v w
  let Q : nativeLieSubalgebraModel (E := D.E) L →L[ℝ] D.E :=
    mfderiv 𝓘(ℝ, nativeLieSubalgebraModel (E := D.E) L) D.I
      ((↑) : nativeLieSubalgebraSubgroup (E := D.E) L → D.G) 1
  have hQ : Q = (nativeLieSubalgebraModel (E := D.E) L).subtype.toContinuousLinearMap :=
    nativeLieSubalgebra_inclusion_mfderiv L
  change Q (nativeLieAdjointGenerator
    (I := 𝓘(ℝ, nativeLieSubalgebraModel (E := D.E) L))
    (G := nativeLieSubalgebraSubgroup (E := D.E) L) v w) =
      nativeLieAdjointGenerator (I := D.I) (G := D.G) (Q v) (Q w) at he
  rw [hQ] at he
  simp only [nativeLieAdjointGenerator_eq_differential] at he
  change (nativeLieAdjointDifferential
    (I := 𝓘(ℝ, nativeLieSubalgebraModel (E := D.E) L))
    (G := nativeLieSubalgebraSubgroup (E := D.E) L) v w).val ∈ F.layer (i+j)
  have he' : (nativeLieAdjointDifferential
      (I := 𝓘(ℝ, nativeLieSubalgebraModel (E := D.E) L))
      (G := nativeLieSubalgebraSubgroup (E := D.E) L) v w).val =
        nativeLieAdjointDifferential (I := D.I) (G := D.G) v.val w.val := he
  exact Eq.mpr (congrArg (fun z : D.E => z ∈ F.layer (i+j)) he')
    (F.bracket i j v.val w.val hv hw)

 theorem affineShear_native_initial_adapted_basis {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    ∃ n : ℕ, ∃ b : Module.Basis (Fin n) ℝ (nativeRationalLayerOrbitData D F 1 ρ hρ).E,
      ∃ weights : Fin n → ℕ, ∀ i,
        1 ≤ weights i ∧ weights i ≤ ℓ ∧
        b i ∈ affineShearNativeInitialFiltration D F ρ hρ (weights i) ∧
        affineShearNativeInitialFiltration D F ρ hρ (weights i+1) ≤ (b.coord i).ker :=
  affineShear_adapted_basis_exists ℓ (affineShearNativeInitialFiltration D F ρ hρ)
    (affineShear_native_initial_antitone D F ρ hρ)
    (affineShear_native_initial_one D F ρ hρ) (affineShear_native_initial_terminal D F ρ hρ)

end Hindman168
