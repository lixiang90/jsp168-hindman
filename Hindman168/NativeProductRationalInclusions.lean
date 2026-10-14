import Hindman168.NativeNilmanifoldData
import Hindman168.NativeProductGlobalLogarithm
import Hindman168.NativeLatticeRationalCoordinates

/-! Actual original diagonal/coordinate inclusions preserve the ACTUAL
original product-lattice rational log span, by genuine positive powers. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_product_rational_diagonal_mem {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) {v : D.E}
    (hv : v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
    (v,v) ∈ nativeSubgroupRationalLogSpan (E := D.E × D.E) (I := D.I.prod D.I) (D.Γ.prod D.Γ) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  obtain ⟨n,hn,hp⟩ := (nativeSubgroupRationalLogSpan_mem_iff_positive_power (I := D.I) D.Γ v).mp hv
  apply (nativeSubgroupRationalLogSpan_mem_iff_positive_power (E := D.E × D.E)
    (I := D.I.prod D.I) (D.Γ.prod D.Γ) (v,v)).mpr
  refine ⟨n,hn,?_⟩
  rw [nativeProductExponential_eq]
  exact ⟨hp,hp⟩

theorem native_product_rational_first_mem {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) {v : D.E}
    (hv : v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
    (v,0) ∈ nativeSubgroupRationalLogSpan (E := D.E × D.E) (I := D.I.prod D.I) (D.Γ.prod D.Γ) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  obtain ⟨n,hn,hp⟩ := (nativeSubgroupRationalLogSpan_mem_iff_positive_power (I := D.I) D.Γ v).mp hv
  apply (nativeSubgroupRationalLogSpan_mem_iff_positive_power (E := D.E × D.E)
    (I := D.I.prod D.I) (D.Γ.prod D.Γ) (v,0)).mpr
  refine ⟨n,hn,?_⟩
  rw [nativeProductExponential_eq]
  change nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v ^ n ∈ D.Γ ∧
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G) 0 ^ n ∈ D.Γ
  refine ⟨hp,?_⟩
  rw [nativeLieExponential_zero,one_pow]
  exact D.Γ.one_mem

end Hindman168
