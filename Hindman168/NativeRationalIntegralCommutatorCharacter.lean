import Hindman168.NativeRationalCommutatorLeftCharacter
import Hindman168.NativeRationalSplitBasisDenominator

/-! GENUINE original horizontal/lattice characters from actual commutators
with rational split vectors. Geometry-only denominator proves integrality;
split-vector exponentials are never asserted to belong to Gamma. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalIntegralCommutatorCharacter {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (i : NativeRationalFirstLayerIndex D L) : D.E →L[ℝ] ℝ :=
  (nativeRationalSplitBasisDenominator D L : ℝ) • nativeRationalCommutatorLeftCharacter D L χ hχ
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (nativeRationalFirstLayerRealBasis D L (Sum.inr i)))

theorem native_rational_integral_commutator_character_evaluation {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (i : NativeRationalFirstLayerIndex D L) (g : D.G) :
    nativeRationalIntegralCommutatorCharacter D L χ hχ i
      (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) =
      (nativeRationalSplitBasisDenominator D L : ℝ)*nativeRationalRelativeCommutatorValue D L χ g
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (nativeRationalFirstLayerRealBasis D L (Sum.inr i))) := by
  change _*nativeRationalCommutatorLeftCharacter D L χ hχ _ _ = _
  rw [native_rational_commutator_left_character_evaluation]

theorem native_rational_integral_commutator_character_kills_two {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (i : NativeRationalFirstLayerIndex D L) :
    L.layer 2 ≤ (nativeRationalIntegralCommutatorCharacter D L χ hχ i).toLinearMap.ker := by
  intro v hv
  change _*nativeRationalCommutatorLeftCharacter D L χ hχ _ v = 0
  have hz := native_rational_commutator_left_character_kills_two D L χ hχ
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (nativeRationalFirstLayerRealBasis D L (Sum.inr i))) hv
  change nativeRationalCommutatorLeftCharacter D L χ hχ _ v = 0 at hz
  exact (congrArg (fun t : ℝ => (nativeRationalSplitBasisDenominator D L : ℝ)*t) hz).trans (mul_zero _)

theorem native_rational_integral_commutator_character_lattice {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (hInt : ∀ γ ∈ (nativeRationalRelativeData D L 1).Γ, ∃ m : ℤ,
      χ (nativeLieGlobalLogarithm (E := (nativeRationalRelativeData D L 1).E)
        (I := (nativeRationalRelativeData D L 1).I) (G := (nativeRationalRelativeData D L 1).G) γ) = (m : ℝ))
    (i : NativeRationalFirstLayerIndex D L) (g : D.G) (hg : g ∈ D.Γ) :
    ∃ z : ℤ, nativeRationalIntegralCommutatorCharacter D L χ hχ i
      (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) = (z : ℝ) := by
  obtain ⟨f,hf,_⟩ := native_continuous_character_linearization (I := D.I) D.Γ
    (nativeRationalRelativeCommutatorValue D L χ g)
    (native_rational_commutator_character_continuous D L χ g)
    (native_rational_commutator_character_mul_right D L χ hχ g)
  have hfInt (j : Fin (Module.finrank ℝ D.E)) :
      ∃ z : ℤ, f (nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ j) = (z : ℝ) := by
    obtain ⟨z,hz⟩ := native_rational_commutator_character_lattice D L χ hInt ⟨g,hg⟩
      ⟨nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ j),
        native_lattice_filtered_smooth_basis_exponential_mem (I := D.I) D.Γ j⟩
    refine ⟨z,?_⟩
    have he := hf (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ j))
    rw [nativeLieGlobalLogarithm_exponential] at he
    exact he.symm.trans hz
  obtain ⟨z,hz⟩ := native_rational_split_basis_scalar_integral D L f.toLinearMap hfInt i
  have he := hf (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
    (nativeRationalFirstLayerRealBasis D L (Sum.inr i)))
  rw [nativeLieGlobalLogarithm_exponential] at he
  refine ⟨z,?_⟩
  rw [native_rational_integral_commutator_character_evaluation,he]
  exact hz

theorem native_rational_integral_commutator_character_horizontal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap)
    (i : NativeRationalFirstLayerIndex D L)
    (hne : (nativeRationalIntegralCommutatorCharacter D L χ hHor.2.1 i).toLinearMap ≠ 0) :
    RoughNativeHorizontalFunctional (I := D.I) D.Γ
      (nativeRationalIntegralCommutatorCharacter D L χ hHor.2.1 i).toLinearMap :=
  ⟨hne,native_rational_kills_two_kills_commutator D L _
      (native_rational_integral_commutator_character_kills_two D L χ hHor.2.1 i),
    native_rational_integral_commutator_character_lattice D L χ hHor.2.1 hHor.2.2 i⟩

end Hindman168
