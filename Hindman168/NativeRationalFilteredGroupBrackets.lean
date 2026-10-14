import Hindman168.NativeRationalFilteredIdeals
import Hindman168.NativeLieAdjointLayer
import Hindman168.NilUpperFaceFiltration

/-! Genuine Lie weight addition integrates to genuine group commutator
weight addition for arbitrary actual rational native Lie filtrations. -/

namespace Hindman168
open scoped Manifold ContDiff commutatorElement
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_filtered_generator_power {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {i j : ℕ} {v w : D.E} (hv : v ∈ F.layer i) (hw : w ∈ F.layer j) (n : ℕ) :
    (nativeLieAdjointGenerator (I := D.I) (G := D.G) v ^ (n+1)) w ∈ F.layer (i+j) := by
  induction n with
  | zero =>
    simpa only [Nat.zero_add,pow_one,nativeLieAdjointGenerator_eq_differential] using F.bracket i j v w hv hw
  | succ n ih =>
    rw [pow_succ',mul_apply_eq_comp]
    rw [nativeLieAdjointGenerator_eq_differential] at ih ⊢
    exact F.antitone (by omega) (F.bracket i (i+j) v _ hv ih)

theorem native_rational_filtered_adjoint_sub {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {i j : ℕ} {v w : D.E} (hv : v ∈ F.layer i) (hw : w ∈ F.layer j) :
    nativeLieAdjoint (I := D.I)
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v) w-w ∈ F.layer (i+j) := by
  have he := nativeLieAdjoint_exponential_sub_one_finite_formula (I := D.I) (G := D.G) v
  have ha : nativeLieAdjoint (I := D.I)
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v) w-w =
      ((nativeLieAdjoint (I := D.I)
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v) : D.E →L[ℝ] D.E)-1) w := by
    simp only [sub_apply,one_apply_eq_self]
  rw [ha,he]
  simp only [_root_.sum_apply,smul_apply]
  apply Submodule.sum_mem
  intro n _
  exact Submodule.smul_mem _ _ (native_rational_filtered_generator_power D F hv hw n)

theorem native_rational_filtered_exponential_commutator {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {i j : ℕ} {v w : D.E} (hv : v ∈ F.layer i) (hw : w ∈ F.layer j) :
    ⁅nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v,
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) w⁆ ∈
        nativeRationalFilteredGroupLayer D F (i+j) := by
  let N := (F.layer (i+j)).restrictScalars ℚ
  have hIdeal : ∀ a ∈ (⊤ : Submodule ℚ D.E), ∀ b ∈ N,
      nativeLieAdjointDifferential (I := D.I) (G := D.G) a b ∈ N := by
    intro a _ b hb
    have ha : a ∈ F.layer 0 := by rw [F.zero]; exact Submodule.mem_top
    change nativeLieAdjointDifferential (I := D.I) (G := D.G) a b ∈ F.layer (i+j)
    simpa only [Nat.zero_add] using F.bracket 0 (i+j) a b ha hb
  have hm := nativeLieGlobalLogarithm_ideal_difference (E := D.E) (I := D.I) (G := D.G)
    ⊤ N le_top hIdeal Submodule.mem_top Submodule.mem_top
    (native_rational_filtered_adjoint_sub D F hv hw)
  apply (native_rational_filtered_group_logarithm_iff D F (i+j) _).mpr
  rw [commutatorElement_def,nativeLieAdjoint_exponential_conjugation]
  exact hm

theorem native_rational_filtered_group_conditions {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    CubeGroupFiltration (nativeRationalFilteredGroupLayer D F) := by
  refine ⟨native_rational_filtered_group_antitone D F,?_⟩
  intro i j g hg h hh
  have hv := (native_rational_filtered_group_logarithm_iff D F i g).mp hg
  have hw := (native_rational_filtered_group_logarithm_iff D F j h).mp hh
  have he := native_rational_filtered_exponential_commutator D F hv hw
  simpa only [nativeLieExponential_globalLogarithm] using he

end Hindman168
