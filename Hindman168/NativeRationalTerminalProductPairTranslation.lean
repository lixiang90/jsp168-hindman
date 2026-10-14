import Hindman168.NativeRationalTerminalProductPairObservable
import Hindman168.NativeRationalTerminalFourierGroupAction
import Hindman168.ProductCosetAction
import Hindman168.NativeRationalRelativeTerminalGeometry

/-! ACTUAL first-terminal eigenlaw and terminal-diagonal invariance
for SAME original translated Fourier conjugate pair, for every translation. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_product_pair_first_equivariant {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (z : nativeRationalFilteredGroupLayer D L (ℓ))
      (q : (D.G × D.G) ⧸ D.Γ.prod D.Γ),
      nativeRationalTerminalProductPairObservable D L k g F (((z : D.G),(1 : D.G)) • q) =
        UnitAddTorus.mFourier k (nativeRationalTerminalTorusProjection D L z) *
          nativeRationalTerminalProductPairObservable D L k g F q := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F z q
  have hc : ∀ r : D.G ⧸ D.Γ, g • ((z : D.G) • r) = (z : D.G) • (g • r) := by
    intro r
    rw [← mul_smul,← mul_smul,Subgroup.mem_center_iff.mp (native_rational_terminal_group_le_center D L z.property) g]
  rw [native_rational_terminal_product_pair_observable_apply,native_rational_terminal_product_pair_observable_apply,
    product_coset_map_product_action]
  simp only [one_smul]
  rw [hc,native_rational_terminal_fourier_group_equivariant,mul_assoc]

theorem native_rational_terminal_product_pair_diagonal_invariant {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (z : nativeRationalFilteredGroupLayer D L (ℓ))
      (q : (D.G × D.G) ⧸ D.Γ.prod D.Γ),
      nativeRationalTerminalProductPairObservable D L k g F (((z : D.G),(z : D.G)) • q) =
        nativeRationalTerminalProductPairObservable D L k g F q := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F z q
  have hcomm : ∀ r : D.G ⧸ D.Γ, g • ((z : D.G) • r) = (z : D.G) • (g • r) := by
    intro r
    rw [← mul_smul,← mul_smul,Subgroup.mem_center_iff.mp (native_rational_terminal_group_le_center D L z.property) g]
  rw [native_rational_terminal_product_pair_observable_apply,native_rational_terminal_product_pair_observable_apply,
    product_coset_map_product_action,hcomm,native_rational_terminal_fourier_group_equivariant,
    native_rational_terminal_fourier_group_equivariant]
  let c := UnitAddTorus.mFourier k (nativeRationalTerminalTorusProjection D L z)
  have hc : c*star c = 1 := by
    rw [Complex.star_def,Complex.mul_conj',unit_torus_fourier_point_norm]
    norm_num
  change (c*_) * star (c*_) = _
  rw [star_mul]
  calc
    _ = (c*star c) * (nativeRationalTerminalFourierProjection D L k F (g • (productCosetMap D.Γ D.Γ q).1) *
      star (nativeRationalTerminalFourierProjection D L k F (productCosetMap D.Γ D.Γ q).2)) := by ring
    _ = _ := by rw [hc,one_mul]

end Hindman168
