import Hindman168.NativeRelativeSquareLatticeGeometry
import Hindman168.NilNaturalCosetMetric

/-! Actual compatible metric on the ORIGINAL relative-square lattice
quotient, from PROVED original restricted-lattice discreteness/cocompactness. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

@[reducible]
noncomputable def nativeRelativeSquareMetric {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    MetricSpace ((nativeRelativeSquareFiltration D d i) ⧸
      (D.Γ.prod D.Γ).comap (nativeRelativeSquareFiltration D d i).subtype) := by
  letI : SecondCountableTopology D.G :=
    (nativeLieGlobalExponentialHomeomorph (I := D.I) (G := D.G)).symm.secondCountableTopology
  letI : SecondCountableTopology (nativeRelativeSquareFiltration D d i) :=
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding
      ((↑) : nativeRelativeSquareFiltration D d i → D.G × D.G)).secondCountableTopology
  letI := native_relative_square_lattice_discrete D d i
  letI := native_relative_square_lattice_cocompact D d hd i
  letI : IsClosed (((D.Γ.prod D.Γ).comap (nativeRelativeSquareFiltration D d i).subtype) :
      Set (nativeRelativeSquareFiltration D d i)) := native_relative_square_lattice_closed D d i
  exact naturalCompactCosetMetric ((D.Γ.prod D.Γ).comap (nativeRelativeSquareFiltration D d i).subtype)

theorem native_relative_square_metric_topology {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    (nativeRelativeSquareMetric D d hd i).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace ((D.Γ.prod D.Γ).comap
        (nativeRelativeSquareFiltration D d i).subtype) := by
  letI : SecondCountableTopology D.G :=
    (nativeLieGlobalExponentialHomeomorph (I := D.I) (G := D.G)).symm.secondCountableTopology
  letI : SecondCountableTopology (nativeRelativeSquareFiltration D d i) :=
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding
      ((↑) : nativeRelativeSquareFiltration D d i → D.G × D.G)).secondCountableTopology
  letI := native_relative_square_lattice_discrete D d i
  letI := native_relative_square_lattice_cocompact D d hd i
  letI : IsClosed (((D.Γ.prod D.Γ).comap (nativeRelativeSquareFiltration D d i).subtype) :
      Set (nativeRelativeSquareFiltration D d i)) := native_relative_square_lattice_closed D d i
  exact naturalCompactCosetMetric_topology ((D.Γ.prod D.Γ).comap (nativeRelativeSquareFiltration D d i).subtype)

theorem native_relative_square_metric_quotientMap {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    @IsOpenQuotientMap (nativeRelativeSquareFiltration D d i)
      ((nativeRelativeSquareFiltration D d i) ⧸ (D.Γ.prod D.Γ).comap
        (nativeRelativeSquareFiltration D d i).subtype)
      inferInstance (nativeRelativeSquareMetric D d hd i).toUniformSpace.toTopologicalSpace (↑) := by
  rw [native_relative_square_metric_topology]
  exact QuotientGroup.isOpenQuotientMap_mk

end Hindman168
