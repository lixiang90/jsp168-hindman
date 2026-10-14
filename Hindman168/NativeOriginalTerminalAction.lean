import Hindman168.NativeOriginalTerminalModel
import Hindman168.NativeNilmanifoldSubspaceAction

/-! ACTUAL ORIGINAL terminal-layer torus action on ORIGINAL G/Gamma.
All central/rational/lattice inputs are PROVED for the original terminal layer. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

abbrev nativeOriginalTerminalIndex {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) :=
  Fin (Module.finrank ℝ (nativeOriginalTerminalModel D d))

noncomputable def nativeOriginalTerminalAction {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    UnitAddTorus (nativeOriginalTerminalIndex D d) → (D.G ⧸ D.Γ) → (D.G ⧸ D.Γ) :=
  nativeNilmanifoldSubspaceAction D (nativeOriginalTerminalModel D d)
    (native_original_terminal_model_le_center D d hd) (native_original_terminal_model_rational D d)

noncomputable def nativeOriginalTerminalTorusProjection {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (z : roughStretchedLowerCentralFiltration D.G d (s*d)) : UnitAddTorus (nativeOriginalTerminalIndex D d) :=
  nativeCentralSubspaceTorusProjection (I := D.I) D.Γ (nativeOriginalTerminalModel D d)
    (native_original_terminal_model_le_center D d hd) (native_original_terminal_model_rational D d)
    ⟨z.val,Eq.mpr (congrArg (fun K : Subgroup D.G => z.val ∈ K)
      (native_original_terminal_central_subgroup_eq D d hd)) z.property⟩

theorem native_original_terminal_action_mk {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (z : roughStretchedLowerCentralFiltration D.G d (s*d)) (q : D.G ⧸ D.Γ) :
    nativeOriginalTerminalAction D d hd (nativeOriginalTerminalTorusProjection D d hd z) q = (z : D.G) • q :=
  native_nilmanifold_subspace_action_mk D _ _ _ _ q

theorem native_original_terminal_action_zero {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (q : D.G ⧸ D.Γ) :
    nativeOriginalTerminalAction D d hd 0 q = q := native_nilmanifold_subspace_action_zero D _ _ _ q

theorem native_original_terminal_action_add {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (a b : UnitAddTorus (nativeOriginalTerminalIndex D d)) (q : D.G ⧸ D.Γ) :
    nativeOriginalTerminalAction D d hd (a+b) q =
      nativeOriginalTerminalAction D d hd a (nativeOriginalTerminalAction D d hd b q) :=
  native_nilmanifold_subspace_action_add D _ _ _ a b q

theorem native_original_terminal_action_commutes {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (a : UnitAddTorus (nativeOriginalTerminalIndex D d)) (g : D.G) (q : D.G ⧸ D.Γ) :
    nativeOriginalTerminalAction D d hd a (g • q) = g • nativeOriginalTerminalAction D d hd a q :=
  native_nilmanifold_subspace_action_commutes D _ _ _ a g q

theorem native_original_terminal_action_continuous {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : UnitAddTorus (nativeOriginalTerminalIndex D d) × (D.G ⧸ D.Γ) =>
      nativeOriginalTerminalAction D d hd p.1 p.2) := native_nilmanifold_subspace_action_continuous D _ _ _

theorem native_original_terminal_action_probability {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (a : UnitAddTorus (nativeOriginalTerminalIndex D d)) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    Measure.map (nativeOriginalTerminalAction D d hd a) (nativeNilmanifoldQuotientProbability D) =
      nativeNilmanifoldQuotientProbability D := native_nilmanifold_subspace_action_probability D _ _ _ a

theorem native_original_terminal_action_integral {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (a : UnitAddTorus (nativeOriginalTerminalIndex D d)) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    ∀ F : (D.G ⧸ D.Γ) → ℂ,
      (∫ q, F (nativeOriginalTerminalAction D d hd a q) ∂nativeNilmanifoldQuotientProbability D) =
        ∫ q, F q ∂nativeNilmanifoldQuotientProbability D := native_nilmanifold_subspace_action_integral D _ _ _ a

end Hindman168
