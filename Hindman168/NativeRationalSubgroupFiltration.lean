import Hindman168.NativeRationalTaylorCoordinates
import Hindman168.RationalRestrictedKernel
import Mathlib.Order.Interval.Finset.Nat

/-! Section 7 filtrations in a possibly proper rational subgroup of the
original native group. Initial layers coincide but need not be ambient top.
All fields are geometric; no source adaptation or factorization is a field.
The level-one kernel changes BOTH initial layers, as the paper requires. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

structure NativeRationalSubgroupFiltration {s : ℕ} (D : NativeNilmanifoldData.{u} s) (ℓ : ℕ) where
  layer : ℕ → Submodule ℝ D.E
  antitone : Antitone layer
  initial : layer 0 = layer 1
  bracket : ∀ i j v w, v ∈ layer i → w ∈ layer j →
    nativeLieAdjointDifferential (I := D.I) (G := D.G) v w ∈ layer (i+j)
  rational : ∀ i, nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (layer i)
  terminal : layer (ℓ+1) = ⊥

noncomputable def nativeRationalSubgroupFiltrationOfFull {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    NativeRationalSubgroupFiltration D ℓ where
  layer := F.layer
  antitone := F.antitone
  initial := F.zero.trans F.one.symm
  bracket := F.bracket
  rational := F.rational
  terminal := F.terminal

noncomputable def nativeRationalSubgroupLayerAlgebra {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ) (i : ℕ) :
    LieSubalgebra ℝ (GroupLieAlgebra D.I D.G) where
  toSubmodule := F.layer i
  lie_mem' := by
    intro v w hv hw
    have hm := F.antitone (Nat.le_add_right i i) (F.bracket i i v w hv hw)
    rw [← nativeLieAdjointGenerator_eq_differential] at hm
    exact (nativeLieAdjointGenerator_eq_native_bracket (I := D.I) (G := D.G) v w) ▸ hm

noncomputable def nativeRationalSubgroupLayer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ) (i : ℕ) : Subgroup D.G :=
  nativeLieSubalgebraSubgroup (nativeRationalSubgroupLayerAlgebra D F i)

theorem native_rational_subgroup_layer_logarithm_iff {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ) (i : ℕ) (g : D.G) :
    g ∈ nativeRationalSubgroupLayer D F i ↔
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g ∈ F.layer i :=
  nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff _ _

theorem native_rational_subgroup_layer_exp_mem {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ) (i : ℕ)
    {v : D.E} (hv : v ∈ F.layer i) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v ∈ nativeRationalSubgroupLayer D F i :=
  ⟨v, hv, rfl⟩

theorem native_rational_subgroup_product_weighted {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    {p q : RoughVectorMvPolynomial σ D.E} {k : ℕ}
    (hp : RoughVectorMvWeightedDegree F.layer p k) (hq : RoughVectorMvWeightedDegree F.layer q k) :
    RoughVectorMvWeightedDegree F.layer (roughNativeProductMvPolynomial (I := D.I) (G := D.G) p q) k := by
  apply rough_parametric_weighted_endpoint
  exact rough_parametric_weighted_picard F.layer F.antitone _ F.bracket _ hq hp _

theorem native_rational_subgroup_polynomial_filtered {s ℓ : ℕ} {σ : Type*} [Fintype σ]
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    RoughFilteredPolynomial (nativeRationalSubgroupLayer D F)
      (fun x : σ → ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) p x)) :=
  native_arbitrary_lie_polynomial_filtered D F.layer F.antitone F.bracket
    (nativeRationalSubgroupLayer D F) (fun i _ hv => native_rational_subgroup_layer_exp_mem D F i hv) p hp

noncomputable def nativeRationalSubgroupLevelKernel {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (j : ℕ) (hj : 1 ≤ j) (phi : D.E →ₗ[ℝ] ℝ)
    (hNext : F.layer (j+1) ≤ phi.ker)
    (hBracket : ∀ a b : ℕ, 0 < a → 0 < b → a+b=j →
      ∀ v ∈ F.layer a, ∀ w ∈ F.layer b,
        phi (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0)
    (hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ q : ℚ, phi v = (q : ℝ)) : NativeRationalSubgroupFiltration D ℓ := by
  classical
  let changed (k : ℕ) : Prop := k=j ∨ (j=1 ∧ k=0)
  let layer (k : ℕ) := if changed k then F.layer k ⊓ phi.ker else F.layer k
  have hLe (k : ℕ) : layer k ≤ F.layer k := by
    dsimp only [layer]; split_ifs
    · exact inf_le_left
    · exact le_rfl
  exact {
    layer := layer
    antitone := by
      intro a b hab
      by_cases ha : changed a
      · by_cases hb : changed b
        · simp only [layer, if_pos ha, if_pos hb]
          exact inf_le_inf_right _ (F.antitone hab)
        · simp only [layer, if_pos ha, if_neg hb]
          have htop : j+1 ≤ b := by
            dsimp only [changed] at ha hb
            rcases ha with ha | ⟨hj1, ha0⟩ <;> omega
          exact le_inf (F.antitone hab) ((F.antitone htop).trans hNext)
      · by_cases hb : changed b
        · simp only [layer, if_neg ha, if_pos hb]
          exact inf_le_left.trans (F.antitone hab)
        · simpa only [layer, if_neg ha, if_neg hb] using F.antitone hab
    initial := by
      by_cases he : j=1
      · have h0 : changed 0 := Or.inr ⟨he,rfl⟩
        have h1 : changed 1 := Or.inl he.symm
        simp only [layer, if_pos h0, if_pos h1, F.initial]
      · have h0 : ¬ changed 0 := by dsimp only [changed]; omega
        have h1 : ¬ changed 1 := by dsimp only [changed]; omega
        simpa only [layer, if_neg h0, if_neg h1] using F.initial
    bracket := by
      intro a b v w hv hw
      have hvOld := hLe a hv
      have hwOld := hLe b hw
      have hOld := F.bracket a b v w hvOld hwOld
      by_cases hab : changed (a+b)
      · simp only [layer, if_pos hab]
        refine ⟨hOld, ?_⟩
        dsimp only [changed] at hab
        rcases hab with hab | ⟨hj1, hab0⟩
        · by_cases ha : a=0
          · subst a
            have hb : b=j := by omega
            subst b
            have hv1 : v ∈ F.layer 1 := F.initial ▸ hvOld
            apply hNext
            simpa only [Nat.add_comm] using F.bracket 1 j v w hv1 hwOld
          · by_cases hb : b=0
            · subst b
              have ha' : a=j := by omega
              subst a
              have hw1 : w ∈ F.layer 1 := F.initial ▸ hwOld
              exact hNext (F.bracket j 1 v w hvOld hw1)
            · exact hBracket a b (by omega) (by omega) hab v hvOld w hwOld
        · have ha : a=0 := by omega
          have hb : b=0 := by omega
          subst a; subst b
          have hv1 : v ∈ F.layer 1 := F.initial ▸ hvOld
          have hw1 : w ∈ F.layer 1 := F.initial ▸ hwOld
          have hm := F.bracket 1 1 v w hv1 hw1
          apply hNext
          simpa only [hj1] using hm
      · simpa only [layer, if_neg hab] using hOld
    rational := by
      intro k
      by_cases hk : changed k
      · simp only [layer, if_pos hk]
        exact rationalRestrictedKernel_rational _ _ _ (F.rational k) hRat
      · simpa only [layer, if_neg hk] using F.rational k
    terminal := by simp only [layer, F.terminal, bot_inf_eq, ite_self] }

theorem native_rational_subgroup_level_kernel_layer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (j : ℕ) (hj : 1 ≤ j) (phi : D.E →ₗ[ℝ] ℝ)
    (hNext : F.layer (j+1) ≤ phi.ker)
    (hBracket : ∀ a b : ℕ, 0 < a → 0 < b → a+b=j →
      ∀ v ∈ F.layer a, ∀ w ∈ F.layer b,
        phi (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0)
    (hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ q : ℚ, phi v = (q : ℝ)) (k : ℕ) :
    (nativeRationalSubgroupLevelKernel D F j hj phi hNext hBracket hRat).layer k =
      if k=j ∨ (j=1 ∧ k=0) then F.layer k ⊓ phi.ker else F.layer k := rfl

noncomputable def nativeRationalSubgroupFiltrationDimension {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 ℓ, Module.finrank ℝ (F.layer k)

theorem native_rational_subgroup_level_kernel_dimension_lt {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (j : ℕ) (hj : 1 ≤ j) (hjTop : j ≤ ℓ) (phi : D.E →ₗ[ℝ] ℝ)
    (hNext : F.layer (j+1) ≤ phi.ker)
    (hBracket : ∀ a b : ℕ, 0 < a → 0 < b → a+b=j →
      ∀ v ∈ F.layer a, ∀ w ∈ F.layer b,
        phi (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0)
    (hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ q : ℚ, phi v = (q : ℝ))
    {z : D.E} (hz : z ∈ F.layer j) (hne : phi z ≠ 0) :
    nativeRationalSubgroupFiltrationDimension D
      (nativeRationalSubgroupLevelKernel D F j hj phi hNext hBracket hRat) <
      nativeRationalSubgroupFiltrationDimension D F := by
  apply Finset.sum_lt_sum
  · intro k _
    apply Submodule.finrank_mono
    rw [native_rational_subgroup_level_kernel_layer]
    split_ifs
    · exact inf_le_left
    · exact le_rfl
  · refine ⟨j, Finset.mem_Icc.mpr ⟨hj,hjTop⟩, ?_⟩
    rw [native_rational_subgroup_level_kernel_layer, if_pos (Or.inl rfl)]
    exact restrictedKernel_finrank_lt _ _ hz hne

end Hindman168
