import Hindman168.NativeDiagonalQuotientLattice
import Hindman168.NilNaturalCosetMetric

/-! ACTUAL compatible metric on the ORIGINAL diagonal-center factor,
from the NOW PROVED actual discrete image lattice and original topology. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] diagonal_center_normal

@[reducible]
noncomputable def nativeDiagonalFactorMetric {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    MetricSpace (nativeDiagonalFactorSpace D) := by
  letI : SecondCountableTopology D.G :=
    (nativeLieGlobalExponentialHomeomorph (I := D.I) (G := D.G)).symm.secondCountableTopology
  letI : IsClosed ((diagonalCenterSubgroup D.G) : Set (D.G × D.G)) := diagonal_center_closed D.G
  letI := native_diagonal_quotient_lattice_discrete D
  letI := native_diagonal_quotient_lattice_cocompact D
  letI := native_diagonal_quotient_lattice_closed D
  exact naturalCompactCosetMetric ((D.Γ.prod D.Γ).map (QuotientGroup.mk' (diagonalCenterSubgroup D.G)))

theorem native_diagonal_factor_metric_topology {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    (nativeDiagonalFactorMetric D).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace ((D.Γ.prod D.Γ).map (QuotientGroup.mk' (diagonalCenterSubgroup D.G))) := by
  letI : SecondCountableTopology D.G :=
    (nativeLieGlobalExponentialHomeomorph (I := D.I) (G := D.G)).symm.secondCountableTopology
  letI : IsClosed ((diagonalCenterSubgroup D.G) : Set (D.G × D.G)) := diagonal_center_closed D.G
  letI := native_diagonal_quotient_lattice_discrete D
  letI := native_diagonal_quotient_lattice_cocompact D
  letI := native_diagonal_quotient_lattice_closed D
  exact naturalCompactCosetMetric_topology _

theorem native_diagonal_factor_metric_quotientMap {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    @IsOpenQuotientMap ((D.G × D.G) ⧸ diagonalCenterSubgroup D.G) (nativeDiagonalFactorSpace D) inferInstance
      (nativeDiagonalFactorMetric D).toUniformSpace.toTopologicalSpace
      ((↑) : ((D.G × D.G) ⧸ diagonalCenterSubgroup D.G) → nativeDiagonalFactorSpace D) := by
  rw [native_diagonal_factor_metric_topology]
  exact QuotientGroup.isOpenQuotientMap_mk

end Hindman168
