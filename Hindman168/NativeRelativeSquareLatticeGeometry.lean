import Hindman168.NativeRelativeSquareRational
import Hindman168.NativeRelativeSquareExponentialSubgroup
import Hindman168.NativeRationalLatticeCompact

/-! Actual original product-lattice intersections in original relative
squares are discrete and cocompact. Rationality and exact exponential
subgroup identity discharge all retained rational-subgroup inputs. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_relative_square_lattice_discrete {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d i : ℕ) :
    DiscreteTopology ((D.Γ.prod D.Γ).comap (nativeRelativeSquareFiltration D d i).subtype) := by
  letI := productLattice_discrete D.Γ D.Γ
  rw [← native_relative_square_native_exponential_subgroup D d i]
  exact nativeLieLattice_intersection_discrete (D.Γ.prod D.Γ) _

theorem native_relative_square_lattice_cocompact {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    CompactSpace ((nativeRelativeSquareFiltration D d i) ⧸
      (D.Γ.prod D.Γ).comap (nativeRelativeSquareFiltration D d i).subtype) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  letI := productLattice_discrete D.Γ D.Γ
  letI := productLattice_quotient_compact D.Γ D.Γ
  rw [← native_relative_square_native_exponential_subgroup D d i]
  exact nativeRationalLieLattice_quotient_compact (D.Γ.prod D.Γ) _
    (native_relative_square_native_model_rational D d hd i)

theorem native_relative_square_lattice_closed {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d i : ℕ) :
    IsClosed (((D.Γ.prod D.Γ).comap (nativeRelativeSquareFiltration D d i).subtype) :
      Set (nativeRelativeSquareFiltration D d i)) := by
  letI := native_relative_square_lattice_discrete D d i
  exact discreteLattice_isClosed _

theorem native_relative_square_lattice_quotient_closedEmbedding {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    Topology.IsClosedEmbedding (subgroupLatticeQuotientInclusion (D.Γ.prod D.Γ)
      (nativeRelativeSquareFiltration D d i)) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  letI := productLattice_discrete D.Γ D.Γ
  letI := productLattice_quotient_compact D.Γ D.Γ
  rw [← native_relative_square_native_exponential_subgroup D d i]
  exact nativeRationalLieLattice_quotient_closedEmbedding (D.Γ.prod D.Γ) _
    (native_relative_square_native_model_rational D d hd i)

theorem native_relative_square_lattice_orbit_compact {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    IsCompact (((↑) : (D.G × D.G) → (D.G × D.G) ⧸ D.Γ.prod D.Γ) ''
      (nativeRelativeSquareFiltration D d i : Set (D.G × D.G))) := by
  letI := native_relative_square_lattice_cocompact D d hd i
  exact subgroupLatticeOrbit_isCompact _ _

theorem native_relative_square_lattice_quotient_metrizable {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    TopologicalSpace.MetrizableSpace ((nativeRelativeSquareFiltration D d i) ⧸
      (D.Γ.prod D.Γ).comap (nativeRelativeSquareFiltration D d i).subtype) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  letI := productLattice_discrete D.Γ D.Γ
  letI := productLattice_quotient_compact D.Γ D.Γ
  rw [← native_relative_square_native_exponential_subgroup D d i]
  exact nativeRationalLieLattice_quotient_metrizable (D.Γ.prod D.Γ) _
    (native_relative_square_native_model_rational D d hd i)

end Hindman168
