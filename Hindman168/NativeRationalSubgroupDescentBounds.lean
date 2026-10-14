import Hindman168.NativeRationalSubgroupFiltration

/-! A level character's nonzero restriction and rational extension produce
an actual rational pivot with value ONE. The strict dimension measure bounds
every finite chain and rules out infinite descent; no source character or
sequential irrationality is inferred from these geometric facts alone. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_subgroup_exists_level_pivot {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (j : ℕ) (phi : D.E →ₗ[ℝ] ℝ)
    (hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ q : ℚ, phi v = (q : ℝ))
    {z : D.E} (hz : z ∈ F.layer j) (hne : phi z ≠ 0) :
    ∃ V : D.E, V ∈ F.layer j ∧
      V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ ∧ phi V = 1 := by
  let W := nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ
  let U : Submodule ℚ D.E := (F.layer j).restrictScalars ℚ ⊓ W
  have he : ∃ v ∈ U, phi v ≠ 0 := by
    by_contra h
    push Not at h
    have hk : Submodule.span ℝ (U : Set D.E) ≤ phi.ker :=
      Submodule.span_le.mpr (fun v hv => h v hv)
    have hs : Submodule.span ℝ (U : Set D.E) = F.layer j := F.rational j
    rw [hs] at hk
    exact hne (hk hz)
  obtain ⟨v, hv, hphi⟩ := he
  obtain ⟨q, hq⟩ := hRat v hv.2
  have hq0 : q ≠ 0 := by
    intro heq
    apply hphi
    rw [hq, heq, Rat.cast_zero]
  have hV : q⁻¹ • v ∈ F.layer j := by
    rw [← Rat.cast_smul_eq_qsmul ℝ]
    exact (F.layer j).smul_mem _ hv.1
  refine ⟨q⁻¹ • v, hV, W.smul_mem _ hv.2, ?_⟩
  rw [← Rat.cast_smul_eq_qsmul ℝ, map_smul, hq, Rat.cast_inv, smul_eq_mul]
  exact inv_mul_cancel₀ (by exact_mod_cast hq0)

theorem native_rational_subgroup_finite_descent_bound {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : ℕ → NativeRationalSubgroupFiltration D ℓ)
    (n : ℕ) (h : ∀ i : ℕ, i < n → nativeRationalSubgroupFiltrationDimension D (F (i+1)) <
      nativeRationalSubgroupFiltrationDimension D (F i)) :
    nativeRationalSubgroupFiltrationDimension D (F n) + n ≤
      nativeRationalSubgroupFiltrationDimension D (F 0) := by
  induction n with
  | zero => omega
  | succ n ih =>
      have hprev := ih (fun i hi => h i (by omega))
      have hlast := h n (by omega)
      omega

theorem native_rational_subgroup_no_infinite_descent {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : ℕ → NativeRationalSubgroupFiltration D ℓ)
    (h : ∀ i : ℕ, nativeRationalSubgroupFiltrationDimension D (F (i+1)) <
      nativeRationalSubgroupFiltrationDimension D (F i)) : False := by
  have hb := native_rational_subgroup_finite_descent_bound D F
    (nativeRationalSubgroupFiltrationDimension D (F 0)+1) (fun i _ => h i)
  omega

end Hindman168
