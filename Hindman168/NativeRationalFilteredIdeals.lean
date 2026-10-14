import Hindman168.NativeRationalLieFiltration
import Hindman168.NativeRealIdealCosets

/-! Every actual finite rational Lie layer is a genuine native Lie ideal;
its normal group layer is its actual original exponential image. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalFilteredLieIdeal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    LieIdeal ℝ (GroupLieAlgebra D.I D.G) where
  toSubmodule := F.layer i
  lie_mem := by
    intro v w hw
    have hv : v ∈ F.layer 0 := by rw [F.zero]; trivial
    have hm := F.bracket 0 i v w hv hw
    rw [Nat.zero_add] at hm
    have he : nativeLieAdjointDifferential (I := D.I) (G := D.G) v w =
        (⁅v,w⁆ : GroupLieAlgebra D.I D.G) := by
      rw [← nativeLieAdjointGenerator_eq_differential]
      exact nativeLieAdjointGenerator_eq_native_bracket (I := D.I) (G := D.G) v w
    exact he ▸ hm

noncomputable def nativeRationalFilteredGroupLayer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) : Subgroup D.G :=
  nativeLieSubalgebraSubgroup (nativeRationalFilteredLieIdeal D F i).toLieSubalgebra

theorem native_rational_filtered_ideal_model {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    nativeLieSubalgebraModel (nativeRationalFilteredLieIdeal D F i).toLieSubalgebra = F.layer i := rfl

theorem native_rational_filtered_group_logarithm_iff {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) (g : D.G) :
    g ∈ nativeRationalFilteredGroupLayer D F i ↔
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g ∈ F.layer i :=
  nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff _ _

theorem native_rational_filtered_group_normal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    (nativeRationalFilteredGroupLayer D F i).Normal :=
  nativeLieIdealSubgroup_normal (nativeRationalFilteredLieIdeal D F i)

theorem native_rational_filtered_group_antitone {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    Antitone (nativeRationalFilteredGroupLayer D F) := by
  intro i j hij g hg
  exact (native_rational_filtered_group_logarithm_iff D F i g).mpr
    (F.antitone hij ((native_rational_filtered_group_logarithm_iff D F j g).mp hg))

theorem native_rational_filtered_group_coset_log_iff {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) (g h : D.G) :
    nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g -
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) h ∈ F.layer i ↔
        h⁻¹*g ∈ nativeRationalFilteredGroupLayer D F i :=
  native_real_ideal_coset_log_iff (nativeRationalFilteredLieIdeal D F i) g h

end Hindman168
