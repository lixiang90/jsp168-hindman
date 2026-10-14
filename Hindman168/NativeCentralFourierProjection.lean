import Hindman168.NativeCentralOrbitObservables
import Hindman168.TorusVerticalFourier
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Genuine continuous vertical Fourier projections on the original metric
nilmanifold. Their eigencharacter laws are proved using the actual action. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

noncomputable def nativeCentralFourierProjection {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ, ℂ) → C(D.G ⧸ D.Γ, ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  intro F
  refine ⟨torusVerticalFourierCoefficient (nativeNilmanifoldCentralAction D) k F, ?_⟩
  unfold torusVerticalFourierCoefficient
  have h : Continuous (fun p : (D.G ⧸ D.Γ) × UnitAddTorus (nativeNilmanifoldCenterIndex D) =>
      UnitAddTorus.mFourier (-k) p.2 * F (nativeNilmanifoldCentralAction D p.2 p.1)) :=
    ((UnitAddTorus.mFourier (-k)).continuous.comp continuous_snd).mul
      (F.continuous.comp ((native_nilmanifold_central_action_continuous D).comp
        (continuous_snd.prodMk continuous_fst)))
  simpa only [torusVerticalFourierCoefficient, Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous
      (μ := Measure.pi (fun _ : nativeNilmanifoldCenterIndex D => AddCircle.haarAddCircle)) h
      (isCompact_univ : IsCompact (Set.univ : Set (UnitAddTorus (nativeNilmanifoldCenterIndex D)))))

theorem native_central_fourier_projection_apply {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (q : D.G ⧸ D.Γ), nativeCentralFourierProjection D k F q =
      ∫ a : UnitAddTorus (nativeNilmanifoldCenterIndex D),
        UnitAddTorus.mFourier (-k) a * F (nativeNilmanifoldCentralAction D a q)
          ∂Measure.pi (fun _ : nativeNilmanifoldCenterIndex D => AddCircle.haarAddCircle) := by
  intro F q
  rfl

theorem native_central_fourier_projection_norm {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
    ∀ F : C(D.G ⧸ D.Γ, ℂ), ‖nativeCentralFourierProjection D k F‖ ≤ ‖F‖ := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  intro F
  apply (ContinuousMap.norm_le _ (norm_nonneg F)).mpr
  intro q
  exact torus_vertical_fourier_coefficient_bound (nativeNilmanifoldCentralAction D) k F q ‖F‖
    F.norm_coe_le_norm

theorem native_central_fourier_projection_equivariant {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (q : D.G ⧸ D.Γ) (a : UnitAddTorus (nativeNilmanifoldCenterIndex D)),
      nativeCentralFourierProjection D k F (nativeNilmanifoldCentralAction D a q) =
        UnitAddTorus.mFourier k a * nativeCentralFourierProjection D k F q := by
  intro F q a
  exact torus_vertical_fourier_coefficient_equivariant (nativeNilmanifoldCentralAction D)
    (native_nilmanifold_central_action_add D) k F q a

theorem native_central_fourier_projection_zero_invariant {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (q : D.G ⧸ D.Γ) (a : UnitAddTorus (nativeNilmanifoldCenterIndex D)),
      nativeCentralFourierProjection D 0 F (nativeNilmanifoldCentralAction D a q) =
        nativeCentralFourierProjection D 0 F q := by
  intro F q a
  rw [native_central_fourier_projection_equivariant, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_mul]

theorem native_central_fourier_projection_nonzero_mean {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) (hk : k ≠ 0) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      (∫ q, nativeCentralFourierProjection D k F q ∂nativeNilmanifoldQuotientProbability D) = 0 := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  obtain ⟨a, ha⟩ := unit_torus_nonzero_fourier_exists k hk
  let J := ∫ q, nativeCentralFourierProjection D k F q ∂nativeNilmanifoldQuotientProbability D
  have h : UnitAddTorus.mFourier k a * J = J := by
    calc
      _ = ∫ q, UnitAddTorus.mFourier k a * nativeCentralFourierProjection D k F q
          ∂nativeNilmanifoldQuotientProbability D := (integral_const_mul _ _).symm
      _ = ∫ q, nativeCentralFourierProjection D k F (nativeNilmanifoldCentralAction D a q)
          ∂nativeNilmanifoldQuotientProbability D := by
        apply integral_congr_ae
        filter_upwards with q
        exact (native_central_fourier_projection_equivariant D k F q a).symm
      _ = J := native_nilmanifold_central_action_integral D a (nativeCentralFourierProjection D k F)
  have hz : (UnitAddTorus.mFourier k a - 1)*J = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)

theorem native_central_fourier_projection_composition {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (j k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ), nativeCentralFourierProjection D j (nativeCentralFourierProjection D k F) =
      if k=j then nativeCentralFourierProjection D k F else 0 := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  ext q
  have h := torus_vertical_fourier_coefficient_of_eigen (nativeNilmanifoldCentralAction D) j k
    (nativeCentralFourierProjection D k F)
    (fun a q => native_central_fourier_projection_equivariant D k F q a) q
  change nativeCentralFourierProjection D j (nativeCentralFourierProjection D k F) q = _ at h
  by_cases he : k=j
  · simpa only [if_pos he] using h
  · simpa only [if_neg he, ContinuousMap.zero_apply] using h

theorem native_central_fourier_projection_idempotent {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ), nativeCentralFourierProjection D k (nativeCentralFourierProjection D k F) =
      nativeCentralFourierProjection D k F := by
  intro F
  simpa only [ite_true] using native_central_fourier_projection_composition D k k F

end Hindman168
