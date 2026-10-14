import Hindman168.NativeRationalFirstLayerCoordinates
import Hindman168.NativeRationalRelativeCharacterSplitting

/-! Integer combinations of the TRUE first-layer coordinates give actual
original characters, integral on the original lattice, killing F_2, and
nonzero whenever the original integer coordinate vector is nonzero. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalFirstLayerIntegerCharacter {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : NativeRationalFirstLayerIndex D L → ℤ) : D.E →L[ℝ] ℝ :=
  ∑ i, (k i : ℝ) • (nativeRationalFirstLayerCoordinate D L i).toContinuousLinearMap

theorem native_rational_first_layer_integer_character_apply {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : NativeRationalFirstLayerIndex D L → ℤ) (v : D.E) :
    nativeRationalFirstLayerIntegerCharacter D L k v =
      ∑ i, (k i : ℝ)*nativeRationalFirstLayerCoordinate D L i v := by
  simp only [nativeRationalFirstLayerIntegerCharacter,sum_apply,
    smul_apply,LinearMap.coe_toContinuousLinearMap',smul_eq_mul]

theorem native_rational_first_layer_integer_character_basis {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : NativeRationalFirstLayerIndex D L → ℤ) (j : NativeRationalFirstLayerIndex D L) :
    nativeRationalFirstLayerIntegerCharacter D L k (nativeRationalFirstLayerRealBasis D L (Sum.inr j)) =
      (k j : ℝ)*(nativeRationalFirstLayerDenominator D L : ℝ) := by
  rw [native_rational_first_layer_integer_character_apply]
  change (∑ i, (k i : ℝ)*((nativeRationalFirstLayerDenominator D L : ℝ)*
    nativeRationalFirstLayerFunctional D L i (nativeRationalFirstLayerRealBasis D L (Sum.inr j)))) = _
  simp only [native_rational_first_layer_functional_basis,Sum.inr.injEq]
  simp

theorem native_rational_first_layer_integer_character_kills_two {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : NativeRationalFirstLayerIndex D L → ℤ) :
    L.layer 2 ≤ (nativeRationalFirstLayerIntegerCharacter D L k).toLinearMap.ker := by
  intro v hv
  change nativeRationalFirstLayerIntegerCharacter D L k v=0
  rw [native_rational_first_layer_integer_character_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [native_rational_first_layer_coordinate_kills_two D L i hv,mul_zero]

theorem native_rational_first_layer_integer_character_lattice {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : NativeRationalFirstLayerIndex D L → ℤ) (g : D.G) (hg : g ∈ D.Γ) :
    ∃ z : ℤ, nativeRationalFirstLayerIntegerCharacter D L k
      (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) = (z : ℝ) := by
  choose z hz using fun i => native_rational_first_layer_coordinate_integral D L i g hg
  refine ⟨∑ i, k i*z i,?_⟩
  rw [native_rational_first_layer_integer_character_apply]
  simp_rw [hz]
  simp only [Int.cast_sum,Int.cast_mul]

theorem native_rational_first_layer_integer_character_nonzero {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : NativeRationalFirstLayerIndex D L → ℤ) (hk : k ≠ 0) :
    (nativeRationalFirstLayerIntegerCharacter D L k).toLinearMap ≠ 0 := by
  intro hz
  apply hk
  funext j
  have he := DFunLike.congr_fun hz (nativeRationalFirstLayerRealBasis D L (Sum.inr j))
  change nativeRationalFirstLayerIntegerCharacter D L k (nativeRationalFirstLayerRealBasis D L (Sum.inr j))=0 at he
  rw [native_rational_first_layer_integer_character_basis] at he
  have hn : (nativeRationalFirstLayerDenominator D L : ℝ) ≠ 0 := by
    exact_mod_cast (native_rational_first_layer_denominator_positive D L).ne'
  have hj := (mul_eq_zero.mp he).resolve_right hn
  exact_mod_cast hj

theorem native_rational_first_layer_integer_character_horizontal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : NativeRationalFirstLayerIndex D L → ℤ) (hk : k ≠ 0) :
    RoughNativeHorizontalFunctional (I := D.I) D.Γ
      (nativeRationalFirstLayerIntegerCharacter D L k).toLinearMap :=
  ⟨native_rational_first_layer_integer_character_nonzero D L k hk,
    native_rational_kills_two_kills_commutator D L _
      (native_rational_first_layer_integer_character_kills_two D L k),
    native_rational_first_layer_integer_character_lattice D L k⟩

theorem native_rational_first_layer_integer_character_norm {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : NativeRationalFirstLayerIndex D L → ℤ) (R : ℝ) (hR : ∀ i, |(k i : ℝ)| ≤ R) :
    ‖nativeRationalFirstLayerIntegerCharacter D L k‖ ≤
      R*(∑ i, ‖(nativeRationalFirstLayerCoordinate D L i).toContinuousLinearMap‖) := by
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hR i) (norm_nonneg _)

theorem native_rational_first_layer_integer_character_grid {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : NativeRationalFirstLayerIndex D L → ℤ) (hk : k ≠ 0)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : ∀ i, |(k i : ℝ)| ≤ R) :
    (nativeRationalFirstLayerIntegerCharacter D L k).toLinearMap ∈
      roughNativeHorizontalCharacterGrid (I := D.I) D.Γ
        (R*(∑ i, ‖(nativeRationalFirstLayerCoordinate D L i).toContinuousLinearMap‖)) := by
  apply rough_native_norm_bounded_horizontal_grid_mem D.Γ _
    (mul_nonneg hR0 (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
  · exact native_rational_first_layer_integer_character_norm D L k R hR
  · exact native_rational_first_layer_integer_character_horizontal D L k hk

end Hindman168
