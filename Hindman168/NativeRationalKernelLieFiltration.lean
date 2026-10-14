import Hindman168.NativeRationalLieFiltration
import Hindman168.RationalRestrictedKernel
import Hindman168.NativeRationalDifferenceCommutatorKernel

/-! GENUINE smaller rational Lie filtration for an ACTUAL rational real
functional killing the original Lie commutator layer. All fields are proved;
this is geometry only and makes NO source/inverse assertion. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_lie_bracket_mem_commutator {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (v w : D.E) :
    nativeLieAdjointDifferential (I := D.I) (G := D.G) v w ∈
      nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 := by
  have hw : w ∈ nativeLieLowerCentralModel (I := D.I) (G := D.G) 0 := by
    rw [nativeLieLowerCentralModel_zero]
    exact Submodule.mem_top
  have he := nativeLieAdjointGenerator_mem_lowerCentral_next (I := D.I) (G := D.G) v hw
  rw [nativeLieAdjointGenerator_eq_differential] at he
  exact he

noncomputable def nativeRationalKernelLieFiltration {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (F : D.E →L[ℝ] ℝ)
    (hF : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ F.toLinearMap.ker)
    (hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ, ∃ q : ℚ, F v = (q : ℝ)) :
    NativeRationalLieFiltration D ℓ := by
  let layer (i : ℕ) := if 2 ≤ i then L.layer i ⊓ F.toLinearMap.ker else L.layer i
  have hLe (i : ℕ) : layer i ≤ L.layer i := by
    by_cases hi : 2 ≤ i
    · simp only [layer,if_pos hi]
      exact inf_le_left
    · simp only [layer,if_neg hi]
      exact le_rfl
  exact
    { layer := layer
      antitone := by
        intro i j hij
        by_cases hi : 2 ≤ i
        · have hj : 2 ≤ j := hi.trans hij
          simp only [layer,if_pos hi,if_pos hj]
          exact inf_le_inf (L.antitone hij) le_rfl
        · by_cases hj : 2 ≤ j
          · simp only [layer,if_neg hi,if_pos hj]
            exact inf_le_left.trans (L.antitone hij)
          · simp only [layer,if_neg hi,if_neg hj]
            exact L.antitone hij
      zero := by simpa only [layer,show ¬2 ≤ 0 by omega,if_false] using L.zero
      one := by simpa only [layer,show ¬2 ≤ 1 by omega,if_false] using L.one
      bracket := by
        intro i j v w hv hw
        have hOld := L.bracket i j v w (hLe i hv) (hLe j hw)
        by_cases hij : 2 ≤ i+j
        · simp only [layer,if_pos hij]
          exact ⟨hOld,hF (native_rational_lie_bracket_mem_commutator D v w)⟩
        · simpa only [layer,if_neg hij] using hOld
      rational := by
        intro i
        by_cases hi : 2 ≤ i
        · simp only [layer,if_pos hi]
          exact rationalRestrictedKernel_rational _ _ _ (L.rational i) hRat
        · simpa only [layer,if_neg hi] using L.rational i
      terminal := by simp only [layer,L.terminal,bot_inf_eq,ite_self] }

theorem native_rational_kernel_lie_filtration_layer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (F : D.E →L[ℝ] ℝ)
    (hF : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ F.toLinearMap.ker)
    (hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ, ∃ q : ℚ, F v = (q : ℝ))
    (i : ℕ) :
    (nativeRationalKernelLieFiltration D L F hF hRat).layer i =
      if 2 ≤ i then L.layer i ⊓ F.toLinearMap.ker else L.layer i := rfl

theorem native_rational_kernel_lie_filtration_layer_le {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (F : D.E →L[ℝ] ℝ)
    (hF : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ F.toLinearMap.ker)
    (hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ, ∃ q : ℚ, F v = (q : ℝ))
    (i : ℕ) : (nativeRationalKernelLieFiltration D L F hF hRat).layer i ≤ L.layer i := by
  rw [native_rational_kernel_lie_filtration_layer]
  split_ifs
  · exact inf_le_left
  · exact le_rfl

end Hindman168
