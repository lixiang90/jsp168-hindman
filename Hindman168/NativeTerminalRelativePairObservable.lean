import Hindman168.NativeTerminalProductPairObservable
import Hindman168.NativeRelativeInclusion
import Hindman168.SubgroupLatticeQuotient

/-! SAME original translated terminal Fourier pair is restricted to
ACTUAL relative restricted-lattice cosets, with genuine compact families. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeRelativeProductCosetMap {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    C((nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ,
      (D.G × D.G) ⧸ D.Γ.prod D.Γ) :=
  ⟨subgroupLatticeQuotientInclusion (D.Γ.prod D.Γ) (nativeRelativeSquareFiltration D d 1),
    subgroupLatticeQuotientInclusion_continuous _ _⟩

theorem native_relative_product_coset_map_equivariant {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (h : (nativeRelativeSquareData D d hd 1).G)
    (q : (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ) :
    nativeRelativeProductCosetMap D d hd (h • q) =
      nativeRelativeGroupInclusion D d hd 1 h • nativeRelativeProductCosetMap D d hd q := by
  induction q using Quotient.inductionOn with
  | _ x => rfl

noncomputable def nativeTerminalRelativePairObservable {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ,ℂ) → C((nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ,ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  exact (nativeTerminalProductPairObservable D d hd k g F).comp (nativeRelativeProductCosetMap D d hd)

theorem native_terminal_relative_pair_observable_apply {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (q : (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ),
      nativeTerminalRelativePairObservable D d hd k g F q =
        nativeTerminalProductPairObservable D d hd k g F (nativeRelativeProductCosetMap D d hd q) := by
  intro F q
  rfl

theorem native_terminal_relative_pair_observable_continuous {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeTerminalRelativePairObservable D d hd k p.1 p.2) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI := productLattice_quotient_compact D.Γ D.Γ
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp
    (((native_terminal_product_pair_observable_continuous D d hd k).comp continuous_fst).prodMk
      ((nativeRelativeProductCosetMap D d hd).continuous.comp continuous_snd))

theorem native_terminal_relative_pair_family_compact {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ)
    (K : Set D.G) (hK : IsCompact K) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsCompact ((fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeTerminalRelativePairObservable D d hd k p.1 p.2) ''
      (K ×ˢ unitLipschitzObservables (D.G ⧸ D.Γ))) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  exact (hK.prod (unit_lipschitz_observables_compact (D.G ⧸ D.Γ))).image
    (native_terminal_relative_pair_observable_continuous D d hd k)

theorem native_terminal_relative_pair_unit_bound {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
      ∀ q : (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ,
        ‖nativeTerminalRelativePairObservable D d hd k g F q‖ ≤ 1 := by
  intro F hF q
  exact native_terminal_product_pair_unit_bound D d hd k g F hF (nativeRelativeProductCosetMap D d hd q)

end Hindman168
