import Hindman168.NativeFinitePiData
import Hindman168.NativeMetricMaskModelTesting

/-! Actual product-lattice coset coordinates, continuous in the specified
native metrics. Metric compatibility is transported by its PROVED topology
identity; no numerical Lipschitz assertion follows from continuity alone. -/
namespace Hindman168
universe u

noncomputable def nativeFinitePiCosetCoordinate {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (i : ι) :
    (nativeFinitePiData D).G ⧸ (nativeFinitePiData D).Γ → (D i).G ⧸ (D i).Γ :=
  Quotient.lift (fun g => (nativeFinitePiGroupEquiv D g i : (D i).G ⧸ (D i).Γ)) (by
    intro g h hgh
    apply QuotientGroup.eq.mpr
    have hc := (native_finite_pi_lattice_mem D (g⁻¹*h)).mp
      (QuotientGroup.leftRel_apply.mp hgh) i
    simpa only [map_mul,map_inv,Pi.mul_apply,Pi.inv_apply] using hc)

theorem native_finite_pi_coset_coordinate_mk {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (i : ι) (g : (nativeFinitePiData D).G) :
    nativeFinitePiCosetCoordinate D i (g : (nativeFinitePiData D).G ⧸ (nativeFinitePiData D).Γ) =
      (nativeFinitePiGroupEquiv D g i : (D i).G ⧸ (D i).Γ) := rfl

theorem native_finite_pi_group_equiv_continuous {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) : Continuous (nativeFinitePiGroupEquiv D) := by
  change Continuous (id : (∀ i, (D i).G) → ∀ i, (D i).G)
  exact continuous_id

theorem native_finite_pi_coset_coordinate_continuous {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (i : ι) : Continuous (nativeFinitePiCosetCoordinate D i) := by
  apply continuous_quot_lift
  exact QuotientGroup.continuous_mk.comp
    ((continuous_apply i).comp (native_finite_pi_group_equiv_continuous D))

theorem native_finite_pi_metric_coset_coordinate_continuous {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (i : ι) :
    letI := (nativeFinitePiData D).metric
    letI : TopologicalSpace ((nativeFinitePiData D).G ⧸ (nativeFinitePiData D).Γ) :=
      (nativeFinitePiData D).metric.toUniformSpace.toTopologicalSpace
    letI := (D i).metric
    letI : TopologicalSpace ((D i).G ⧸ (D i).Γ) := (D i).metric.toUniformSpace.toTopologicalSpace
    Continuous (nativeFinitePiCosetCoordinate D i) := by
  rw [←nativeNilmanifold_metric_topology (nativeFinitePiData D),←nativeNilmanifold_metric_topology (D i)]
  exact native_finite_pi_coset_coordinate_continuous D i

end Hindman168
