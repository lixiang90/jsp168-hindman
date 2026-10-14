import Hindman168.NativeRationalTerminalProductPairObservable
import Hindman168.NativeRationalRelativeInclusion
import Hindman168.SubgroupLatticeQuotient

/-! SAME original translated terminal Fourier pair is restricted to
ACTUAL relative restricted-lattice cosets, with genuine compact families. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeRationalRelativeProductCosetMap {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    C((nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ,
      (D.G × D.G) ⧸ D.Γ.prod D.Γ) :=
  ⟨subgroupLatticeQuotientInclusion (D.Γ.prod D.Γ) (nativeRationalRelativeGroupLayer D L 1),
    subgroupLatticeQuotientInclusion_continuous _ _⟩

theorem native_rational_relative_product_coset_map_equivariant {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (h : (nativeRationalRelativeData D L 1).G)
    (q : (nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ) :
    nativeRationalRelativeProductCosetMap D L (h • q) =
      nativeRationalRelativeGroupInclusion D L 1 h • nativeRationalRelativeProductCosetMap D L q := by
  induction q using Quotient.inductionOn with
  | _ x => rfl

noncomputable def nativeRationalTerminalRelativePairObservable {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ,ℂ) → C((nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ,ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  exact (nativeRationalTerminalProductPairObservable D L k g F).comp (nativeRationalRelativeProductCosetMap D L)

theorem native_rational_terminal_relative_pair_observable_apply {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (q : (nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ),
      nativeRationalTerminalRelativePairObservable D L k g F q =
        nativeRationalTerminalProductPairObservable D L k g F (nativeRationalRelativeProductCosetMap D L q) := by
  intro F q
  rfl

theorem native_rational_terminal_relative_pair_observable_continuous {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeRationalTerminalRelativePairObservable D L k p.1 p.2) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI := productLattice_quotient_compact D.Γ D.Γ
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp
    (((native_rational_terminal_product_pair_observable_continuous D L k).comp continuous_fst).prodMk
      ((nativeRationalRelativeProductCosetMap D L).continuous.comp continuous_snd))

theorem native_rational_terminal_relative_pair_family_compact {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ)
    (K : Set D.G) (hK : IsCompact K) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsCompact ((fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeRationalTerminalRelativePairObservable D L k p.1 p.2) ''
      (K ×ˢ unitLipschitzObservables (D.G ⧸ D.Γ))) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  exact (hK.prod (unit_lipschitz_observables_compact (D.G ⧸ D.Γ))).image
    (native_rational_terminal_relative_pair_observable_continuous D L k)

theorem native_rational_terminal_relative_pair_unit_bound {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
      ∀ q : (nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ,
        ‖nativeRationalTerminalRelativePairObservable D L k g F q‖ ≤ 1 := by
  intro F hF q
  exact native_rational_terminal_product_pair_unit_bound D L k g F hF (nativeRationalRelativeProductCosetMap D L q)

end Hindman168
