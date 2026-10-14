import Hindman168.NativeRationalSubgroupFiltration
import Hindman168.NativeFiniteProductExponential
import Hindman168.NativeFiniteProductLattice

/-! Coordinatewise ORIGINAL rational logarithms are rational for the ACTUAL
product lattice. Common positive powers are constructed, not assumed. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] nativeFiniteProductTopologicalSpace nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three




@[reducible]
def nativeFiniteProductRationalModule {E : Type*} [NormedAddCommGroup E] [Module ℚ E] :
    (n : ℕ) → Module ℚ (nativeFiniteProduct E n)
  | 0 => inferInstanceAs (Module ℚ E)
  | n+1 => by
    letI := nativeFiniteProductRationalModule (E := E) n
    exact inferInstanceAs (Module ℚ (nativeFiniteProduct E n × E))

attribute [local instance] nativeFiniteProductRationalModule

theorem native_finite_product_rational_span_mem {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n : ℕ) (v : nativeFiniteProduct D.E n)
    (hv : ∀ k, nativeFiniteProductCoordinate n v k ∈
      nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    letI := nativeFiniteProductSimplyConnected (I := D.I) (G := D.G) n
    v ∈ nativeSubgroupRationalLogSpan (E := nativeFiniteProduct D.E n)
      (I := nativeFiniteProductCorners D.I n) (nativeFiniteProductLattice D.Γ n) := by
  induction n with
  | zero => exact hv 0
  | succ n ih =>
    letI := nativeFiniteProductLieGroup (I := D.I) (G := D.G) (n+1)
    letI := nativeFiniteProductBoundaryless (I := D.I) (G := D.G) (n+1)
    letI := nativeFiniteProductSimplyConnected (I := D.I) (G := D.G) n
    letI := nativeFiniteProductSimplyConnected (I := D.I) (G := D.G) (n+1)
    have hfirst := ih v.1 (fun k => by
      simpa only [nativeFiniteProductCoordinate_castSucc] using hv k.castSucc)
    have hlast : v.2 ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ := by
      simpa only [nativeFiniteProductCoordinate_last] using hv (Fin.last (n+1))
    obtain ⟨a,ha,hpa⟩ := (nativeSubgroupRationalLogSpan_mem_iff_positive_power
      (E := nativeFiniteProduct D.E n) (G := nativeFiniteProduct D.G n)
      (I := nativeFiniteProductCorners D.I n) (nativeFiniteProductLattice D.Γ n) v.1).mp hfirst
    obtain ⟨b,hb,hpb⟩ := (nativeSubgroupRationalLogSpan_mem_iff_positive_power
      (I := D.I) D.Γ v.2).mp hlast
    apply (nativeSubgroupRationalLogSpan_mem_iff_positive_power
      (E := nativeFiniteProduct D.E (n+1)) (G := nativeFiniteProduct D.G (n+1))
      (I := nativeFiniteProductCorners D.I (n+1)) (nativeFiniteProductLattice D.Γ (n+1)) v).mpr
    refine ⟨a*b,Nat.mul_pos ha hb,?_⟩
    change (nativeLieExponential (I := (nativeFiniteProductCorners D.I n).prod D.I)
      (G := nativeFiniteProduct D.G n × D.G) (v.1,v.2))^(a*b) ∈
        (nativeFiniteProductLattice D.Γ n).prod D.Γ
    rw [nativeProductExponential_eq]
    change (nativeLieExponential (I := nativeFiniteProductCorners D.I n)
      (G := nativeFiniteProduct D.G n) v.1)^(a*b) ∈ nativeFiniteProductLattice D.Γ n ∧
      (nativeLieExponential (I := D.I) (G := D.G) v.2)^(a*b) ∈ D.Γ
    constructor
    · rw [pow_mul]
      exact (nativeFiniteProductLattice D.Γ n).pow_mem hpa b
    · rw [Nat.mul_comm a b, pow_mul]
      exact D.Γ.pow_mem hpb a

end Hindman168
