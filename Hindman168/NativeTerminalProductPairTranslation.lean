import Hindman168.NativeTerminalProductPairObservable
import Hindman168.NativeOriginalTerminalFourierGroupAction
import Hindman168.ProductCosetAction

/-! ACTUAL first-terminal eigenlaw and terminal-diagonal invariance
for SAME original translated Fourier conjugate pair, for every translation. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_terminal_product_pair_first_equivariant {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (z : roughStretchedLowerCentralFiltration D.G d (s*d))
      (q : (D.G × D.G) ⧸ D.Γ.prod D.Γ),
      nativeTerminalProductPairObservable D d hd k g F (((z : D.G),(1 : D.G)) • q) =
        UnitAddTorus.mFourier k (nativeOriginalTerminalTorusProjection D d hd z) *
          nativeTerminalProductPairObservable D d hd k g F q := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F z q
  have hc : ∀ r : D.G ⧸ D.Γ, g • ((z : D.G) • r) = (z : D.G) • (g • r) := by
    intro r
    rw [← mul_smul,← mul_smul,Subgroup.mem_center_iff.mp (native_original_terminal_group_le_center D d hd z.property) g]
  rw [native_terminal_product_pair_observable_apply,native_terminal_product_pair_observable_apply,
    product_coset_map_product_action]
  simp only [one_smul]
  rw [hc,native_original_terminal_fourier_group_equivariant,mul_assoc]

theorem native_terminal_product_pair_diagonal_invariant {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (z : roughStretchedLowerCentralFiltration D.G d (s*d))
      (q : (D.G × D.G) ⧸ D.Γ.prod D.Γ),
      nativeTerminalProductPairObservable D d hd k g F (((z : D.G),(z : D.G)) • q) =
        nativeTerminalProductPairObservable D d hd k g F q := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F z q
  have hcomm : ∀ r : D.G ⧸ D.Γ, g • ((z : D.G) • r) = (z : D.G) • (g • r) := by
    intro r
    rw [← mul_smul,← mul_smul,Subgroup.mem_center_iff.mp (native_original_terminal_group_le_center D d hd z.property) g]
  rw [native_terminal_product_pair_observable_apply,native_terminal_product_pair_observable_apply,
    product_coset_map_product_action,hcomm,native_original_terminal_fourier_group_equivariant,
    native_original_terminal_fourier_group_equivariant]
  let c := UnitAddTorus.mFourier k (nativeOriginalTerminalTorusProjection D d hd z)
  have hc : c*star c = 1 := by
    rw [Complex.star_def,Complex.mul_conj',unit_torus_fourier_point_norm]
    norm_num
  change (c*_) * star (c*_) = _
  rw [star_mul]
  calc
    _ = (c*star c) * (nativeOriginalTerminalFourierProjection D d hd k F (g • (productCosetMap D.Γ D.Γ q).1) *
      star (nativeOriginalTerminalFourierProjection D d hd k F (productCosetMap D.Γ D.Γ q).2)) := by ring
    _ = _ := by rw [hc,one_mul]

end Hindman168
