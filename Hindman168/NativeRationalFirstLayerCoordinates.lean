import Hindman168.NativeRationalFirstLayerIntegral
import Hindman168.NativeRationalFilteredGroupGeometry

/-! Actual lattice-integral first-layer coordinates of G/F_2. The kernel
is SAME true F_2, not merely the lower-central commutator layer. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff BigOperators Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalFirstLayerCoordinates {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (g : D.G) :
    NativeRationalFirstLayerIndex D L → ℝ :=
  fun i => nativeRationalFirstLayerCoordinate D L i
    (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g)

theorem native_rational_first_layer_coordinates_mul {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (g h : D.G) :
    nativeRationalFirstLayerCoordinates D L (g*h) =
      nativeRationalFirstLayerCoordinates D L g+nativeRationalFirstLayerCoordinates D L h := by
  funext i
  exact nativeLieLogarithmCharacter_mul (nativeRationalFirstLayerCoordinate D L i)
    (native_rational_kills_two_kills_commutator D L _ (native_rational_first_layer_coordinate_kills_two D L i)) g h

theorem native_rational_first_layer_coordinates_one {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    nativeRationalFirstLayerCoordinates D L 1=0 := by
  funext i
  simp only [nativeRationalFirstLayerCoordinates,nativeLieGlobalLogarithm_one,map_zero,Pi.zero_apply]

theorem native_rational_first_layer_coordinates_zpow {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (g : D.G) (n : ℤ) :
    nativeRationalFirstLayerCoordinates D L (g^n) =
      fun i => (n : ℝ)*nativeRationalFirstLayerCoordinates D L g i := by
  let φ : D.G →* Multiplicative (NativeRationalFirstLayerIndex D L → ℝ) := {
    toFun := fun g => Multiplicative.ofAdd (nativeRationalFirstLayerCoordinates D L g)
    map_one' := native_rational_first_layer_coordinates_one D L
    map_mul' := native_rational_first_layer_coordinates_mul D L }
  have he := φ.map_zpow g n
  change nativeRationalFirstLayerCoordinates D L (g^n) = n • nativeRationalFirstLayerCoordinates D L g at he
  funext i
  simpa only [Pi.smul_apply,zsmul_eq_mul] using congrFun he i

theorem native_rational_first_layer_coordinates_continuous {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    Continuous (nativeRationalFirstLayerCoordinates D L) := by
  apply continuous_pi
  intro i
  exact (nativeRationalFirstLayerCoordinate D L i).continuous_of_finiteDimensional.comp
    (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)).continuous

theorem native_rational_first_layer_model_kernel {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (v : D.E) :
    (∀ i, nativeRationalFirstLayerCoordinate D L i v=0) ↔ v ∈ L.layer 2 := by
  constructor
  · intro hv
    have hq : (nativeRationalFirstLayerDenominator D L : ℝ) ≠ 0 := by
      exact_mod_cast (native_rational_first_layer_denominator_positive D L).ne'
    have hc : ∀ i, (nativeRationalFirstLayerRealBasis D L).repr v (Sum.inr i)=0 := by
      intro i
      have he := hv i
      change (nativeRationalFirstLayerDenominator D L : ℝ)*nativeRationalFirstLayerFunctional D L i v=0 at he
      have hz := (mul_eq_zero.mp he).resolve_left hq
      simpa only [native_rational_first_layer_functional_coord,Basis.coord_apply] using hz
    have he := (nativeRationalFirstLayerRealBasis D L).sum_repr v
    rw [Fintype.sum_sum_type] at he
    have hz : (∑ i : NativeRationalFirstLayerIndex D L,
        (nativeRationalFirstLayerRealBasis D L).repr v (Sum.inr i) • nativeRationalFirstLayerRealBasis D L (Sum.inr i))=0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hc,zero_smul]
    rw [hz,add_zero] at he
    rw [← he]
    apply Submodule.sum_mem
    intro i _
    exact (L.layer 2).smul_mem _ (native_rational_first_layer_basis_inl_mem D L i)
  · intro hv i
    exact native_rational_first_layer_coordinate_kills_two D L i hv

theorem native_rational_first_layer_coordinates_kernel {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (g : D.G) :
    nativeRationalFirstLayerCoordinates D L g=0 ↔ g ∈ nativeRationalFilteredGroupLayer D L 2 := by
  rw [funext_iff]
  change (∀ i, nativeRationalFirstLayerCoordinate D L i
    (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g)=0) ↔ _
  rw [native_rational_first_layer_model_kernel,native_rational_filtered_group_logarithm_iff]

end Hindman168
