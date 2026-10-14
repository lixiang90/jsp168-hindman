import Hindman168.NativeRationalTerminalOrbitObservables
import Hindman168.TorusVerticalFourier
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Actual terminal FourierProjection for ANY original finite rational Lie filtration.
All original central/rational/lattice/action/canonical-Haar inputs are
PROVED using SAME actual terminal layer and SAME original specified metric. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

noncomputable def nativeRationalTerminalFourierProjection {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ, ℂ) → C(D.G ⧸ D.Γ, ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  intro F
  refine ⟨torusVerticalFourierCoefficient (nativeRationalTerminalAction D L) k F, ?_⟩
  unfold torusVerticalFourierCoefficient
  have h : Continuous (fun p : (D.G ⧸ D.Γ) × UnitAddTorus (nativeRationalTerminalIndex D L) =>
      UnitAddTorus.mFourier (-k) p.2 * F (nativeRationalTerminalAction D L p.2 p.1)) :=
    ((UnitAddTorus.mFourier (-k)).continuous.comp continuous_snd).mul
      (F.continuous.comp ((native_rational_terminal_action_continuous D L).comp
        (continuous_snd.prodMk continuous_fst)))
  simpa only [torusVerticalFourierCoefficient, Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous
      (μ := Measure.pi (fun _ : nativeRationalTerminalIndex D L => AddCircle.haarAddCircle)) h
      (isCompact_univ : IsCompact (Set.univ : Set (UnitAddTorus (nativeRationalTerminalIndex D L)))))

theorem native_rational_terminal_fourier_projection_apply {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (q : D.G ⧸ D.Γ), nativeRationalTerminalFourierProjection D L k F q =
      ∫ a : UnitAddTorus (nativeRationalTerminalIndex D L),
        UnitAddTorus.mFourier (-k) a * F (nativeRationalTerminalAction D L a q)
          ∂Measure.pi (fun _ : nativeRationalTerminalIndex D L => AddCircle.haarAddCircle) := by
  intro F q
  rfl

theorem native_rational_terminal_fourier_projection_norm {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
    ∀ F : C(D.G ⧸ D.Γ, ℂ), ‖nativeRationalTerminalFourierProjection D L k F‖ ≤ ‖F‖ := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  intro F
  apply (ContinuousMap.norm_le _ (norm_nonneg F)).mpr
  intro q
  exact torus_vertical_fourier_coefficient_bound (nativeRationalTerminalAction D L) k F q ‖F‖
    F.norm_coe_le_norm

theorem native_rational_terminal_fourier_projection_equivariant {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (q : D.G ⧸ D.Γ) (a : UnitAddTorus (nativeRationalTerminalIndex D L)),
      nativeRationalTerminalFourierProjection D L k F (nativeRationalTerminalAction D L a q) =
        UnitAddTorus.mFourier k a * nativeRationalTerminalFourierProjection D L k F q := by
  intro F q a
  exact torus_vertical_fourier_coefficient_equivariant (nativeRationalTerminalAction D L)
    (native_rational_terminal_action_add D L) k F q a

theorem native_rational_terminal_fourier_projection_zero_invariant {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (q : D.G ⧸ D.Γ) (a : UnitAddTorus (nativeRationalTerminalIndex D L)),
      nativeRationalTerminalFourierProjection D L 0 F (nativeRationalTerminalAction D L a q) =
        nativeRationalTerminalFourierProjection D L 0 F q := by
  intro F q a
  rw [native_rational_terminal_fourier_projection_equivariant, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_mul]

theorem native_rational_terminal_fourier_projection_nonzero_mean {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      (∫ q, nativeRationalTerminalFourierProjection D L k F q ∂nativeNilmanifoldQuotientProbability D) = 0 := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  obtain ⟨a, ha⟩ := unit_torus_nonzero_fourier_exists k hk
  let J := ∫ q, nativeRationalTerminalFourierProjection D L k F q ∂nativeNilmanifoldQuotientProbability D
  have h : UnitAddTorus.mFourier k a * J = J := by
    calc
      _ = ∫ q, UnitAddTorus.mFourier k a * nativeRationalTerminalFourierProjection D L k F q
          ∂nativeNilmanifoldQuotientProbability D := (integral_const_mul _ _).symm
      _ = ∫ q, nativeRationalTerminalFourierProjection D L k F (nativeRationalTerminalAction D L a q)
          ∂nativeNilmanifoldQuotientProbability D := by
        apply integral_congr_ae
        filter_upwards with q
        exact (native_rational_terminal_fourier_projection_equivariant D L k F q a).symm
      _ = J := native_rational_terminal_action_integral D L a (nativeRationalTerminalFourierProjection D L k F)
  have hz : (UnitAddTorus.mFourier k a - 1)*J = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)

theorem native_rational_terminal_fourier_projection_composition {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (j k : nativeRationalTerminalIndex D L → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ), nativeRationalTerminalFourierProjection D L j (nativeRationalTerminalFourierProjection D L k F) =
      if k=j then nativeRationalTerminalFourierProjection D L k F else 0 := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  ext q
  have h := torus_vertical_fourier_coefficient_of_eigen (nativeRationalTerminalAction D L) j k
    (nativeRationalTerminalFourierProjection D L k F)
    (fun a q => native_rational_terminal_fourier_projection_equivariant D L k F q a) q
  change nativeRationalTerminalFourierProjection D L j (nativeRationalTerminalFourierProjection D L k F) q = _ at h
  by_cases he : k=j
  · simpa only [if_pos he] using h
  · simpa only [if_neg he, ContinuousMap.zero_apply] using h

theorem native_rational_terminal_fourier_projection_idempotent {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ), nativeRationalTerminalFourierProjection D L k (nativeRationalTerminalFourierProjection D L k F) =
      nativeRationalTerminalFourierProjection D L k F := by
  intro F
  simpa only [ite_true] using native_rational_terminal_fourier_projection_composition D L k k F

end Hindman168
