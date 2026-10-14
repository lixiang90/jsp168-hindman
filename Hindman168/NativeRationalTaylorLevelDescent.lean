import Hindman168.NativeRationalTaylorCoordinates
import Hindman168.RationalRestrictedKernel
import Mathlib.Order.Interval.Finset.Nat

/-! The geometric j>=2 descent in 07_cube_limits.tex 293--305.
Only layer j changes. Higher-layer annihilation and the actual bracket
annihilation conditions prove nesting and every bracket inclusion. Rationality
and STRICT finite dimension decrease are proved; no source correction,
character production, sequential factorization or local Haar law is assumed. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalTaylorLevelKernel {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (j : ℕ) (hj : 2 ≤ j) (phi : D.E →ₗ[ℝ] ℝ)
    (hNext : F.layer (j+1) ≤ phi.ker)
    (hBracket : ∀ a b : ℕ, 0 < a → 0 < b → a+b=j →
      ∀ v ∈ F.layer a, ∀ w ∈ F.layer b,
        phi (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0)
    (hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ q : ℚ, phi v = (q : ℝ)) : NativeRationalLieFiltration D ℓ := by
  let layer (k : ℕ) := if k=j then F.layer k ⊓ phi.ker else F.layer k
  have hLe (k : ℕ) : layer k ≤ F.layer k := by
    by_cases hk : k=j
    · simp only [layer, if_pos hk]; exact inf_le_left
    · simp only [layer, if_neg hk]; exact le_rfl
  exact {
    layer := layer
    antitone := by
      intro a b hab
      by_cases ha : a=j
      · subst a
        by_cases hb : b=j
        · subst b; exact le_rfl
        · simp only [layer, if_pos rfl, if_neg hb]
          exact le_inf (F.antitone hab) ((F.antitone (by omega : j+1 ≤ b)).trans hNext)
      · by_cases hb : b=j
        · subst b
          simp only [layer, if_neg ha, if_pos rfl]
          exact inf_le_left.trans (F.antitone hab)
        · simp only [layer, if_neg ha, if_neg hb]
          exact F.antitone hab
    zero := by simpa only [layer, if_neg (by omega : 0 ≠ j)] using F.zero
    one := by simpa only [layer, if_neg (by omega : 1 ≠ j)] using F.one
    bracket := by
      intro a b v w hv hw
      have hvOld := hLe a hv
      have hwOld := hLe b hw
      have hOld := F.bracket a b v w hvOld hwOld
      by_cases hab : a+b=j
      · simp only [layer, if_pos hab]
        refine ⟨hOld, ?_⟩
        by_cases ha : a=0
        · subst a
          have hb : b=j := by omega
          subst b
          have hv1 : v ∈ F.layer 1 := by rw [F.one]; exact Submodule.mem_top
          apply hNext
          simpa only [Nat.add_comm] using F.bracket 1 j v w hv1 hwOld
        · by_cases hb : b=0
          · subst b
            have ha' : a=j := by omega
            subst a
            have hw1 : w ∈ F.layer 1 := by rw [F.one]; exact Submodule.mem_top
            have hm := F.bracket j 1 v w hvOld hw1
            exact hNext hm
          · exact hBracket a b (by omega) (by omega) hab v hvOld w hwOld
      · simpa only [layer, if_neg hab] using hOld
    rational := by
      intro k
      by_cases hk : k=j
      · simp only [layer, if_pos hk]
        exact rationalRestrictedKernel_rational _ _ _ (F.rational k) hRat
      · simpa only [layer, if_neg hk] using F.rational k
    terminal := by simp only [layer, F.terminal, bot_inf_eq, ite_self] }

theorem native_rational_taylor_level_kernel_layer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (j : ℕ) (hj : 2 ≤ j) (phi : D.E →ₗ[ℝ] ℝ)
    (hNext : F.layer (j+1) ≤ phi.ker)
    (hBracket : ∀ a b : ℕ, 0 < a → 0 < b → a+b=j →
      ∀ v ∈ F.layer a, ∀ w ∈ F.layer b,
        phi (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0)
    (hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ q : ℚ, phi v = (q : ℝ)) (k : ℕ) :
    (nativeRationalTaylorLevelKernel D F j hj phi hNext hBracket hRat).layer k =
      if k=j then F.layer k ⊓ phi.ker else F.layer k := rfl

theorem native_rational_taylor_level_kernel_layer_le {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (j : ℕ) (hj : 2 ≤ j) (phi : D.E →ₗ[ℝ] ℝ)
    (hNext : F.layer (j+1) ≤ phi.ker)
    (hBracket : ∀ a b : ℕ, 0 < a → 0 < b → a+b=j →
      ∀ v ∈ F.layer a, ∀ w ∈ F.layer b,
        phi (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0)
    (hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ q : ℚ, phi v = (q : ℝ)) (k : ℕ) :
    (nativeRationalTaylorLevelKernel D F j hj phi hNext hBracket hRat).layer k ≤ F.layer k := by
  rw [native_rational_taylor_level_kernel_layer]
  split_ifs
  · exact inf_le_left
  · exact le_rfl

theorem native_rational_taylor_level_kernel_strict_dimension {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (j : ℕ) (hj : 2 ≤ j) (phi : D.E →ₗ[ℝ] ℝ)
    (hNext : F.layer (j+1) ≤ phi.ker)
    (hBracket : ∀ a b : ℕ, 0 < a → 0 < b → a+b=j →
      ∀ v ∈ F.layer a, ∀ w ∈ F.layer b,
        phi (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0)
    (hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ q : ℚ, phi v = (q : ℝ))
    {z : D.E} (hz : z ∈ F.layer j) (hne : phi z ≠ 0) :
    Module.finrank ℝ ((nativeRationalTaylorLevelKernel D F j hj phi hNext hBracket hRat).layer j) <
      Module.finrank ℝ (F.layer j) := by
  rw [native_rational_taylor_level_kernel_layer, if_pos rfl]
  exact restrictedKernel_finrank_lt _ _ hz hne

theorem native_rational_taylor_level_kernel_total_dimension_lt {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (j : ℕ) (hj : 2 ≤ j) (hjTop : j ≤ ℓ) (phi : D.E →ₗ[ℝ] ℝ)
    (hNext : F.layer (j+1) ≤ phi.ker)
    (hBracket : ∀ a b : ℕ, 0 < a → 0 < b → a+b=j →
      ∀ v ∈ F.layer a, ∀ w ∈ F.layer b,
        phi (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0)
    (hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ q : ℚ, phi v = (q : ℝ))
    {z : D.E} (hz : z ∈ F.layer j) (hne : phi z ≠ 0) :
    (∑ k ∈ Finset.Icc 1 ℓ, Module.finrank ℝ
      ((nativeRationalTaylorLevelKernel D F j hj phi hNext hBracket hRat).layer k)) <
      ∑ k ∈ Finset.Icc 1 ℓ, Module.finrank ℝ (F.layer k) := by
  apply Finset.sum_lt_sum
  · intro k _
    exact Submodule.finrank_mono (native_rational_taylor_level_kernel_layer_le D F j hj phi hNext hBracket hRat k)
  · exact ⟨j, Finset.mem_Icc.mpr ⟨by omega, hjTop⟩,
      native_rational_taylor_level_kernel_strict_dimension D F j hj phi hNext hBracket hRat hz hne⟩

end Hindman168
