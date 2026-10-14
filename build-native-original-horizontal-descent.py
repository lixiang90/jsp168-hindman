from pathlib import Path

src=Path('Hindman168/RoughNativeNormalizedObstructionBadFamily.lean').read_text(encoding='utf-8')
start=src.index('theorem rough_native_normalized_obstruction_bad_family')
stop=src.index(' := by',start)
header=src[start:stop]
begin=header.index('    (D :')
end=header.index('    (q : ℕ)',begin)
header=header[:begin]+'''    (D : NativeNilmanifoldData.{u} step) (χ : D.E →ₗ[ℝ] ℝ)
    (hHor : RoughNativeHorizontalFunctional (I := D.I) D.Γ χ)
'''+header[end:]
header=header.replace('rough_native_normalized_obstruction_bad_family','native_original_horizontal_kernel_descent')
header=header.replace('    let hQ :=', '''    let S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G) := ⊤
    let hS := native_original_top_lie_rational D
    let hχ := native_original_horizontal_top_bracket D χ hHor
    let hΓ := hHor.2.2
    let hQ :=''')
result='''import Hindman168.NativeOriginalHorizontalKernelGeometry

/-! ACTUAL original horizontal character alone supplies all rational/geometry
inputs to proved kernel descent. No supplied pivot, lattice period, subgroup
or inverse. Finite canonical children and budgets precede all raw sources. -/
namespace Hindman168
open Filter MvPolynomial
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

'''+header+''' := by
  let S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G) := ⊤
  let hS := native_original_top_lie_rational D
  let hχ := native_original_horizontal_top_bracket D χ hHor
  obtain ⟨v,hv⟩ := DFunLike.ne_iff.mp hHor.1
  have hv0 : χ v ≠ 0 := by simpa only [LinearMap.zero_apply] using hv
  exact rough_native_normalized_obstruction_bad_family D S hS χ hχ hHor.2.2 v
    (show v ∈ nativeLieSubalgebraModel S from (Submodule.mem_top : v ∈ (⊤ : Submodule ℝ D.E))) hv0
    q A0 C B hA0 hC hB Lip c η hc hη Scale Z hScale hr

end Hindman168
'''
Path('Hindman168/NativeOriginalHorizontalKernelDescent.lean').write_text(result,encoding='utf-8')
