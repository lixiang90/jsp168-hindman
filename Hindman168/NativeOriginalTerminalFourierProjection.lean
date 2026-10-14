import Hindman168.NativeOriginalTerminalOrbitObservables
import Hindman168.TorusVerticalFourier
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! ACTUAL ORIGINAL TERMINAL-LAYER specialization. All action inputs are
proved from original terminal centrality/rationality/lattice coordinates.
Frequencies are on the ACTUAL original terminal-layer torus.
 Genuine continuous vertical Fourier projections on the original metric
nilmanifold. Their eigencharacter laws are proved using the actual action. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

noncomputable def nativeOriginalTerminalFourierProjection {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (k : nativeOriginalTerminalIndex D d → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ, ℂ) → C(D.G ⧸ D.Γ, ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  intro F
  refine ⟨torusVerticalFourierCoefficient (nativeOriginalTerminalAction D d hd) k F, ?_⟩
  unfold torusVerticalFourierCoefficient
  have h : Continuous (fun p : (D.G ⧸ D.Γ) × UnitAddTorus (nativeOriginalTerminalIndex D d) =>
      UnitAddTorus.mFourier (-k) p.2 * F (nativeOriginalTerminalAction D d hd p.2 p.1)) :=
    ((UnitAddTorus.mFourier (-k)).continuous.comp continuous_snd).mul
      (F.continuous.comp ((native_original_terminal_action_continuous D d hd).comp
        (continuous_snd.prodMk continuous_fst)))
  simpa only [torusVerticalFourierCoefficient, Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous
      (μ := Measure.pi (fun _ : nativeOriginalTerminalIndex D d => AddCircle.haarAddCircle)) h
      (isCompact_univ : IsCompact (Set.univ : Set (UnitAddTorus (nativeOriginalTerminalIndex D d)))))

theorem native_original_terminal_fourier_projection_apply {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (k : nativeOriginalTerminalIndex D d → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (q : D.G ⧸ D.Γ), nativeOriginalTerminalFourierProjection D d hd k F q =
      ∫ a : UnitAddTorus (nativeOriginalTerminalIndex D d),
        UnitAddTorus.mFourier (-k) a * F (nativeOriginalTerminalAction D d hd a q)
          ∂Measure.pi (fun _ : nativeOriginalTerminalIndex D d => AddCircle.haarAddCircle) := by
  intro F q
  rfl

theorem native_original_terminal_fourier_projection_norm {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (k : nativeOriginalTerminalIndex D d → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
    ∀ F : C(D.G ⧸ D.Γ, ℂ), ‖nativeOriginalTerminalFourierProjection D d hd k F‖ ≤ ‖F‖ := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  intro F
  apply (ContinuousMap.norm_le _ (norm_nonneg F)).mpr
  intro q
  exact torus_vertical_fourier_coefficient_bound (nativeOriginalTerminalAction D d hd) k F q ‖F‖
    F.norm_coe_le_norm

theorem native_original_terminal_fourier_projection_equivariant {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (k : nativeOriginalTerminalIndex D d → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (q : D.G ⧸ D.Γ) (a : UnitAddTorus (nativeOriginalTerminalIndex D d)),
      nativeOriginalTerminalFourierProjection D d hd k F (nativeOriginalTerminalAction D d hd a q) =
        UnitAddTorus.mFourier k a * nativeOriginalTerminalFourierProjection D d hd k F q := by
  intro F q a
  exact torus_vertical_fourier_coefficient_equivariant (nativeOriginalTerminalAction D d hd)
    (native_original_terminal_action_add D d hd) k F q a

theorem native_original_terminal_fourier_projection_zero_invariant {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (q : D.G ⧸ D.Γ) (a : UnitAddTorus (nativeOriginalTerminalIndex D d)),
      nativeOriginalTerminalFourierProjection D d hd 0 F (nativeOriginalTerminalAction D d hd a q) =
        nativeOriginalTerminalFourierProjection D d hd 0 F q := by
  intro F q a
  rw [native_original_terminal_fourier_projection_equivariant, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_mul]

theorem native_original_terminal_fourier_projection_nonzero_mean {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (k : nativeOriginalTerminalIndex D d → ℤ) (hk : k ≠ 0) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      (∫ q, nativeOriginalTerminalFourierProjection D d hd k F q ∂nativeNilmanifoldQuotientProbability D) = 0 := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  obtain ⟨a, ha⟩ := unit_torus_nonzero_fourier_exists k hk
  let J := ∫ q, nativeOriginalTerminalFourierProjection D d hd k F q ∂nativeNilmanifoldQuotientProbability D
  have h : UnitAddTorus.mFourier k a * J = J := by
    calc
      _ = ∫ q, UnitAddTorus.mFourier k a * nativeOriginalTerminalFourierProjection D d hd k F q
          ∂nativeNilmanifoldQuotientProbability D := (integral_const_mul _ _).symm
      _ = ∫ q, nativeOriginalTerminalFourierProjection D d hd k F (nativeOriginalTerminalAction D d hd a q)
          ∂nativeNilmanifoldQuotientProbability D := by
        apply integral_congr_ae
        filter_upwards with q
        exact (native_original_terminal_fourier_projection_equivariant D d hd k F q a).symm
      _ = J := native_original_terminal_action_integral D d hd a (nativeOriginalTerminalFourierProjection D d hd k F)
  have hz : (UnitAddTorus.mFourier k a - 1)*J = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)

theorem native_original_terminal_fourier_projection_composition {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (j k : nativeOriginalTerminalIndex D d → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ), nativeOriginalTerminalFourierProjection D d hd j (nativeOriginalTerminalFourierProjection D d hd k F) =
      if k=j then nativeOriginalTerminalFourierProjection D d hd k F else 0 := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  ext q
  have h := torus_vertical_fourier_coefficient_of_eigen (nativeOriginalTerminalAction D d hd) j k
    (nativeOriginalTerminalFourierProjection D d hd k F)
    (fun a q => native_original_terminal_fourier_projection_equivariant D d hd k F q a) q
  change nativeOriginalTerminalFourierProjection D d hd j (nativeOriginalTerminalFourierProjection D d hd k F) q = _ at h
  by_cases he : k=j
  · simpa only [if_pos he] using h
  · simpa only [if_neg he, ContinuousMap.zero_apply] using h

theorem native_original_terminal_fourier_projection_idempotent {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (k : nativeOriginalTerminalIndex D d → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ), nativeOriginalTerminalFourierProjection D d hd k (nativeOriginalTerminalFourierProjection D d hd k F) =
      nativeOriginalTerminalFourierProjection D d hd k F := by
  intro F
  simpa only [ite_true] using native_original_terminal_fourier_projection_composition D d hd k k F

end Hindman168
