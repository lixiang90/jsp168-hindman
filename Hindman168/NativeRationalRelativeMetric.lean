import Hindman168.NativeRationalRelativeLatticeGeometry
import Hindman168.NilNaturalCosetMetric

/-! Genuine native structures and original lattice quotient for arbitrary finite rational Lie-filtered relative layers. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

@[reducible]
noncomputable def nativeRationalRelativeMetric {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    MetricSpace ((nativeRationalRelativeGroupLayer D F i) ⧸
      (D.Γ.prod D.Γ).comap (nativeRationalRelativeGroupLayer D F i).subtype) := by
  letI : SecondCountableTopology D.G :=
    (nativeLieGlobalExponentialHomeomorph (I := D.I) (G := D.G)).symm.secondCountableTopology
  letI : SecondCountableTopology (nativeRationalRelativeGroupLayer D F i) :=
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding
      ((↑) : nativeRationalRelativeGroupLayer D F i → D.G × D.G)).secondCountableTopology
  letI := native_rational_relative_lattice_discrete D F i
  letI := native_rational_relative_lattice_cocompact D F i
  letI : IsClosed (((D.Γ.prod D.Γ).comap (nativeRationalRelativeGroupLayer D F i).subtype) :
      Set (nativeRationalRelativeGroupLayer D F i)) := native_rational_relative_lattice_closed D F i
  exact naturalCompactCosetMetric ((D.Γ.prod D.Γ).comap (nativeRationalRelativeGroupLayer D F i).subtype)

theorem native_rational_relative_metric_topology {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    (nativeRationalRelativeMetric D F i).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace ((D.Γ.prod D.Γ).comap
        (nativeRationalRelativeGroupLayer D F i).subtype) := by
  letI : SecondCountableTopology D.G :=
    (nativeLieGlobalExponentialHomeomorph (I := D.I) (G := D.G)).symm.secondCountableTopology
  letI : SecondCountableTopology (nativeRationalRelativeGroupLayer D F i) :=
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding
      ((↑) : nativeRationalRelativeGroupLayer D F i → D.G × D.G)).secondCountableTopology
  letI := native_rational_relative_lattice_discrete D F i
  letI := native_rational_relative_lattice_cocompact D F i
  letI : IsClosed (((D.Γ.prod D.Γ).comap (nativeRationalRelativeGroupLayer D F i).subtype) :
      Set (nativeRationalRelativeGroupLayer D F i)) := native_rational_relative_lattice_closed D F i
  exact naturalCompactCosetMetric_topology ((D.Γ.prod D.Γ).comap (nativeRationalRelativeGroupLayer D F i).subtype)

theorem native_rational_relative_metric_quotientMap {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    @IsOpenQuotientMap (nativeRationalRelativeGroupLayer D F i)
      ((nativeRationalRelativeGroupLayer D F i) ⧸ (D.Γ.prod D.Γ).comap
        (nativeRationalRelativeGroupLayer D F i).subtype)
      inferInstance (nativeRationalRelativeMetric D F i).toUniformSpace.toTopologicalSpace (↑) := by
  rw [native_rational_relative_metric_topology]
  exact QuotientGroup.isOpenQuotientMap_mk

end Hindman168
