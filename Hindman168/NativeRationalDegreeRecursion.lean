import Hindman168.NativeRationalTerminalGroupFiltration
import Hindman168.NativeRationalRelativeRationalFiltration

/-! Genuine geometric degree recursion: actual relative native data followed
by the actual terminal quotient, retaining ALL projected original layers.
The construction terminates geometrically; no quantitative inverse is claimed. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalDegreeReducedData {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) : NativeNilmanifoldData.{u} s :=
  nativeRationalTerminalQuotientData (nativeRationalRelativeData D F 1) (nativeRelativeRationalLieFiltration D F)

noncomputable def nativeDegreeReducedRationalLieFiltration {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    NativeRationalLieFiltration (nativeRationalDegreeReducedData D F) (ℓ-1) :=
  nativeTerminalRationalLieFiltration (nativeRationalRelativeData D F 1) (nativeRelativeRationalLieFiltration D F)

theorem native_rational_degree_reduced_actual_layers {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    (nativeDegreeReducedRationalLieFiltration D F).layer i =
      (nativeRationalRelativeLieLayer D F i).map
        (nativeRationalTerminalModelProjection (nativeRationalRelativeData D F 1)
          (nativeRelativeRationalLieFiltration D F)).toLinearMap := rfl

theorem native_rational_degree_reduced_strict (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ℓ-1 < ℓ := by omega

noncomputable def nativeIteratedRationalDegreeReduction {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    (n : ℕ) → Σ D' : NativeNilmanifoldData.{u} s, NativeRationalLieFiltration D' (ℓ-n)
  | 0 => ⟨D,F⟩
  | n+1 => by
      let prev := nativeIteratedRationalDegreeReduction D F n
      let nextD := nativeRationalDegreeReducedData prev.1 prev.2
      let nextF := nativeDegreeReducedRationalLieFiltration prev.1 prev.2
      exact ⟨nextD,by simpa only [Nat.sub_sub] using nextF⟩

theorem native_rational_degree_zero_group_subsingleton {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D 0) : Subsingleton D.G := by
  have hTopBot : (⊤ : Subgroup D.G) = ⊥ :=
    (native_rational_filtered_group_one D F).symm.trans (native_rational_filtered_group_terminal D F)
  constructor
  intro g h
  have hg : g = 1 := by
    have hm : g ∈ (⊤ : Subgroup D.G) := Subgroup.mem_top g
    rw [hTopBot,Subgroup.mem_bot] at hm
    exact hm
  have hh : h = 1 := by
    have hm : h ∈ (⊤ : Subgroup D.G) := Subgroup.mem_top h
    rw [hTopBot,Subgroup.mem_bot] at hm
    exact hm
  exact hg.trans hh.symm

theorem native_rational_degree_recursion_terminates {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    Subsingleton (nativeIteratedRationalDegreeReduction D F ℓ).1.G := by
  let finalStage := nativeIteratedRationalDegreeReduction D F ℓ
  have hF : NativeRationalLieFiltration finalStage.1 0 := by
    simpa only [Nat.sub_self] using finalStage.2
  exact native_rational_degree_zero_group_subsingleton finalStage.1 hF

end Hindman168
