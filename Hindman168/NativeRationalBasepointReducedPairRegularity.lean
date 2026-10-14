import Hindman168.NativeBasepointObservable
import Hindman168.NativeRationalTerminalReducedPairCompact
import Hindman168.CompactLipschitzApproximation

/-! Actual reduced pairs after BOTH original basepoint and linear-shift
translations form a compact family in the actual reduced specified metric.
ONE finite spatial Lipschitz approximant family works for all original inputs. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_basepoint_reduced_pair_continuous {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalDegreeReducedData D L).metric
    letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
      (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : (D.G × D.G) × C(D.G ⧸ D.Γ,ℂ) =>
      nativeRationalTerminalReducedPairObservable D L k p.1.2 (nativeBasepointObservable D p.1.1 p.2)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  have hBase : Continuous (fun p : (D.G × D.G) × C(D.G ⧸ D.Γ,ℂ) =>
      nativeBasepointObservable D p.1.1 p.2) :=
    (native_basepoint_observable_continuous D).comp (continuous_fst.fst.prodMk continuous_snd)
  have hPair : Continuous (fun p : (D.G × D.G) × C(D.G ⧸ D.Γ,ℂ) =>
      (p.1.2,nativeBasepointObservable D p.1.1 p.2)) := continuous_fst.snd.prodMk hBase
  letI := (nativeRationalDegreeReducedData D L).metric
  letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeRationalDegreeReducedData D L)
  have hObs : Continuous (fun q : D.G × C(D.G ⧸ D.Γ,ℂ) =>
      nativeRationalTerminalReducedPairObservable D L k q.1 q.2) :=
    native_rational_terminal_reduced_pair_observable_continuous D L k
  have hComp := hObs.comp hPair
  convert hComp using 1
  rfl

theorem native_rational_basepoint_reduced_pair_family_compact {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ)
    (K T : Set D.G) (hK : IsCompact K) (hT : IsCompact T) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalDegreeReducedData D L).metric
    letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
      (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
    IsCompact ((fun p : (D.G × D.G) × C(D.G ⧸ D.Γ,ℂ) =>
      nativeRationalTerminalReducedPairObservable D L k p.1.2 (nativeBasepointObservable D p.1.1 p.2)) ''
        ((K ×ˢ T) ×ˢ unitLipschitzObservables (D.G ⧸ D.Γ))) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalDegreeReducedData D L).metric
  letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
  exact ((hK.prod hT).prod (unit_lipschitz_observables_compact (D.G ⧸ D.Γ))).image
    (native_rational_basepoint_reduced_pair_continuous D L k)

theorem native_rational_basepoint_reduced_pair_regular_approximation {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ)
    (K T : Set D.G) (hK : IsCompact K) (hT : IsCompact T) (ε : ℝ) (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalDegreeReducedData D L).metric
    letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
      (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
      native_nilmanifold_metric_quotient_compact (nativeRationalDegreeReducedData D L)
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∃ P : Finset C((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ,ℂ),
        (∀ H ∈ P, (∀ y, ‖H y‖ ≤ B) ∧ LipschitzWith (Real.toNNReal C) H) ∧
        ∀ r ∈ K, ∀ t ∈ T, ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          ∃ H ∈ P, ‖nativeRationalTerminalReducedPairObservable D L k t (nativeBasepointObservable D r F)-H‖ < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalDegreeReducedData D L).metric
  letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeRationalDegreeReducedData D L)
  obtain ⟨B,C,hB,hC,P,hP,hClose⟩ := compact_family_bounded_lipschitz_approximation _ _
    (native_rational_basepoint_reduced_pair_family_compact D L k K T hK hT) ε hε
  refine ⟨B,C,hB,hC,P,hP,?_⟩
  intro r hr t ht F hF
  exact hClose _ ⟨((r,t),F),⟨⟨hr,ht⟩,hF⟩,rfl⟩

end Hindman168
