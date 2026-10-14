import Hindman168.NativeRelativeReducedLieInitial
import Hindman168.NativeRelativeReducedLayerRational
import Hindman168.RoughNativeStretchedLieTerminal

/-! Finite rational native Lie filtrations retain actual original layers.
The datum contains algebraic/geometric conditions only, no inverse theorem.
Both the original stretched filtration and its actual reduced IMAGE
filtration satisfy every field. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

structure NativeRationalLieFiltration {s : ℕ} (D : NativeNilmanifoldData.{u} s) (ℓ : ℕ) where
  layer : ℕ → Submodule ℝ D.E
  antitone : Antitone layer
  zero : layer 0 = ⊤
  one : layer 1 = ⊤
  bracket : ∀ i j v w, v ∈ layer i → w ∈ layer j →
    nativeLieAdjointDifferential (I := D.I) (G := D.G) v w ∈ layer (i+j)
  rational : ∀ i, nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (layer i)
  terminal : layer (ℓ+1) = ⊥

noncomputable def nativeOriginalRationalLieFiltration {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) : NativeRationalLieFiltration D (s*d) where
  layer := roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d
  antitone := rough_native_stretched_lie_antitone d hd
  zero := rough_native_stretched_lie_initial d hd 0 (Nat.zero_le d)
  one := rough_native_stretched_lie_initial d hd 1 hd
  bracket := fun _ _ _ _ hv hw => rough_native_stretched_lie_bracket d hd hv hw
  rational := fun i => nativeLieLowerCentralModel_lattice_rational (I := D.I) D.Γ ((i ⌈/⌉ d)-1)
  terminal := rough_native_stretched_lie_terminal d hd D.step_le

noncomputable def nativeReducedRationalLieFiltration {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    NativeRationalLieFiltration (nativeRelativeReducedData D d hd) (s*d-1) where
  layer := nativeRelativeReducedLieFiltration D d hd
  antitone := native_relative_reduced_lie_filtration_antitone D d hd
  zero := native_relative_reduced_lie_filtration_zero D d hd
  one := native_relative_reduced_lie_filtration_one D d hd
  bracket := fun _ _ _ _ hv hw => native_relative_reduced_lie_filtration_bracket D d hd hv hw
  rational := native_relative_reduced_layer_rational D d hd
  terminal := native_relative_reduced_lie_filtration_terminal D d hd _ (by omega)

theorem native_original_rational_lie_filtration_layer {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    (nativeOriginalRationalLieFiltration D d hd).layer i =
      roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d i := rfl

theorem native_reduced_rational_lie_filtration_layer {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    (nativeReducedRationalLieFiltration D d hd).layer i = nativeRelativeReducedLieFiltration D d hd i := rfl

end Hindman168
