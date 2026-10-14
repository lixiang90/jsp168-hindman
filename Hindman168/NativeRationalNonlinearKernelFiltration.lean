import Hindman168.NativeRationalKernelLieFiltration
import Hindman168.NativeRationalDifferenceExtension
import Mathlib.Order.Interval.Finset.Nat

/-! The ACTUAL nonzero difference / zero pairing case constructs a genuine
smaller rational filtration with STRICTLY smaller natural nonlinearity.
No source factorization or inverse for the new filtration is assumed. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff BigOperators
universe u

noncomputable def nativeRationalNonlinearKernelFiltration {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap)
    (hzero : ∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0) : NativeRationalLieFiltration D ℓ :=
  nativeRationalKernelLieFiltration D L (nativeRationalDifferenceExtension D L χ)
    (native_rational_difference_extension_kills_commutator D L χ hHor.2.1 hzero)
    (fun v hv => native_rational_difference_extension_rational_value D L χ hHor.2.2 ⟨v,hv⟩)

theorem native_rational_nonlinear_kernel_filtration_layer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap)
    (hzero : ∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0) (i : ℕ) :
    (nativeRationalNonlinearKernelFiltration D L χ hHor hzero).layer i =
      if 2 ≤ i then L.layer i ⊓ (nativeRationalDifferenceExtension D L χ).toLinearMap.ker else L.layer i := rfl

theorem native_rational_nonlinear_kernel_filtration_layer_le {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap)
    (hzero : ∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0) (i : ℕ) :
    (nativeRationalNonlinearKernelFiltration D L χ hHor hzero).layer i ≤ L.layer i :=
  native_rational_kernel_lie_filtration_layer_le D L _ _ _ i

theorem native_rational_nonlinear_kernel_filtration_two_dimension_lt {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap)
    (hzero : ∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0)
    (hne : nativeRationalRelativeDifferenceCharacter D L χ ≠ 0) :
    Module.finrank ℝ ((nativeRationalNonlinearKernelFiltration D L χ hHor hzero).layer 2) <
      Module.finrank ℝ (L.layer 2) := by
  rw [native_rational_nonlinear_kernel_filtration_layer,if_pos le_rfl]
  obtain ⟨v,hv,hFv⟩ := native_rational_difference_extension_nonzero_on_two D L χ hne
  exact restrictedKernel_finrank_lt _ _ hv hFv

noncomputable def nativeRationalFiltrationNonlinearity {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) : ℕ :=
  ∑ i ∈ Finset.Icc 2 ℓ, Module.finrank ℝ (L.layer i)

theorem native_rational_nonlinear_kernel_filtration_nonlinearity_lt {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap)
    (hzero : ∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0)
    (hne : nativeRationalRelativeDifferenceCharacter D L χ ≠ 0) :
    nativeRationalFiltrationNonlinearity D (nativeRationalNonlinearKernelFiltration D L χ hHor hzero) <
      nativeRationalFiltrationNonlinearity D L := by
  unfold nativeRationalFiltrationNonlinearity
  apply Finset.sum_lt_sum
  · intro i _
    exact Submodule.finrank_mono (native_rational_nonlinear_kernel_filtration_layer_le D L χ hHor hzero i)
  · exact ⟨2,Finset.mem_Icc.mpr ⟨le_rfl,hdeg⟩,
      native_rational_nonlinear_kernel_filtration_two_dimension_lt D L χ hHor hzero hne⟩

end Hindman168
