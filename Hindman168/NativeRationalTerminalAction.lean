import Hindman168.NativeRationalFilteredTerminal
import Hindman168.NativeNilmanifoldSubspaceAction

/-! Actual terminal Action for ANY original finite rational Lie filtration.
All original central/rational/lattice/action/canonical-Haar inputs are
PROVED using SAME actual terminal layer and SAME original specified metric. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

abbrev nativeRationalTerminalIndex {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :=
  Fin (Module.finrank ℝ ((L.layer ℓ)))

noncomputable def nativeRationalTerminalAction {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    UnitAddTorus (nativeRationalTerminalIndex D L) → (D.G ⧸ D.Γ) → (D.G ⧸ D.Γ) :=
  nativeNilmanifoldSubspaceAction D ((L.layer ℓ))
    (native_rational_filtered_terminal_central D L) (L.rational ℓ)

noncomputable def nativeRationalTerminalTorusProjection {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (z : nativeRationalFilteredGroupLayer D L ℓ) : UnitAddTorus (nativeRationalTerminalIndex D L) :=
  nativeCentralSubspaceTorusProjection (I := D.I) D.Γ ((L.layer ℓ))
    (native_rational_filtered_terminal_central D L) (L.rational ℓ)
    ⟨z.val,Eq.mpr (congrArg (fun K : Subgroup D.G => z.val ∈ K)
      (native_rational_terminal_subgroup_eq D L)) z.property⟩

theorem native_rational_terminal_action_mk {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (z : nativeRationalFilteredGroupLayer D L ℓ) (q : D.G ⧸ D.Γ) :
    nativeRationalTerminalAction D L (nativeRationalTerminalTorusProjection D L z) q = (z : D.G) • q :=
  native_nilmanifold_subspace_action_mk D _ _ _ _ q

theorem native_rational_terminal_action_zero {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (q : D.G ⧸ D.Γ) :
    nativeRationalTerminalAction D L 0 q = q := native_nilmanifold_subspace_action_zero D _ _ _ q

theorem native_rational_terminal_action_add {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (a b : UnitAddTorus (nativeRationalTerminalIndex D L)) (q : D.G ⧸ D.Γ) :
    nativeRationalTerminalAction D L (a+b) q =
      nativeRationalTerminalAction D L a (nativeRationalTerminalAction D L b q) :=
  native_nilmanifold_subspace_action_add D _ _ _ a b q

theorem native_rational_terminal_action_commutes {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (a : UnitAddTorus (nativeRationalTerminalIndex D L)) (g : D.G) (q : D.G ⧸ D.Γ) :
    nativeRationalTerminalAction D L a (g • q) = g • nativeRationalTerminalAction D L a q :=
  native_nilmanifold_subspace_action_commutes D _ _ _ a g q

theorem native_rational_terminal_action_continuous {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : UnitAddTorus (nativeRationalTerminalIndex D L) × (D.G ⧸ D.Γ) =>
      nativeRationalTerminalAction D L p.1 p.2) := native_nilmanifold_subspace_action_continuous D _ _ _

theorem native_rational_terminal_action_probability {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (a : UnitAddTorus (nativeRationalTerminalIndex D L)) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    Measure.map (nativeRationalTerminalAction D L a) (nativeNilmanifoldQuotientProbability D) =
      nativeNilmanifoldQuotientProbability D := native_nilmanifold_subspace_action_probability D _ _ _ a

theorem native_rational_terminal_action_integral {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (a : UnitAddTorus (nativeRationalTerminalIndex D L)) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    ∀ F : (D.G ⧸ D.Γ) → ℂ,
      (∫ q, F (nativeRationalTerminalAction D L a q) ∂nativeNilmanifoldQuotientProbability D) =
        ∫ q, F q ∂nativeNilmanifoldQuotientProbability D := native_nilmanifold_subspace_action_integral D _ _ _ a

end Hindman168
