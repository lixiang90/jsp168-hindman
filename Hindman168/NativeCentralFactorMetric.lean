import Hindman168.NativeCentralFactorTopology
import Hindman168.NativeCenterQuotientNativeLogarithm
import Hindman168.NilNaturalCosetMetric

/-! An ACTUAL compatible metric on the original central factor/image lattice. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_central_quotient_secondCountable {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    SecondCountableTopology (D.G ⧸ Subgroup.center D.G) :=
  (nativeCenterQuotientExponentialHomeomorph (I := D.I) (G := D.G)).symm.secondCountableTopology

@[reducible]
noncomputable def nativeCentralFactorMetric {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    MetricSpace (nativeCentralFactorSpace D) := by
  letI := native_central_quotient_secondCountable D
  letI := nativeCenterQuotient_t2Space (I := D.I) (G := D.G)
  letI := nativeLattice_center_quotient_image_discrete (I := D.I) D.Γ
  letI := native_central_factor_compact D
  letI : IsClosed (D.Γ.map (QuotientGroup.mk' (Subgroup.center D.G)) : Set (D.G ⧸ Subgroup.center D.G)) :=
    Subgroup.isClosed_of_discrete
  exact naturalCompactCosetMetric (D.Γ.map (QuotientGroup.mk' (Subgroup.center D.G)))

theorem native_central_factor_metric_topology {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    (nativeCentralFactorMetric D).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace (D.Γ.map (QuotientGroup.mk' (Subgroup.center D.G))) := by
  letI := native_central_quotient_secondCountable D
  letI := nativeCenterQuotient_t2Space (I := D.I) (G := D.G)
  letI := nativeLattice_center_quotient_image_discrete (I := D.I) D.Γ
  letI := native_central_factor_compact D
  letI : IsClosed (D.Γ.map (QuotientGroup.mk' (Subgroup.center D.G)) : Set (D.G ⧸ Subgroup.center D.G)) :=
    Subgroup.isClosed_of_discrete
  exact naturalCompactCosetMetric_topology _

theorem native_central_factor_metric_quotientMap {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    @IsOpenQuotientMap (D.G ⧸ Subgroup.center D.G) (nativeCentralFactorSpace D) inferInstance
      (nativeCentralFactorMetric D).toUniformSpace.toTopologicalSpace
      ((↑) : (D.G ⧸ Subgroup.center D.G) → nativeCentralFactorSpace D) := by
  rw [native_central_factor_metric_topology]
  exact QuotientGroup.isOpenQuotientMap_mk

end Hindman168
