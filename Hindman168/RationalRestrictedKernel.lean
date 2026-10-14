import Hindman168.RationalSubspaceFunctional

/-! A real functional with rational values on a rational subspace has
a kernel spanned by its rational vectors, also after restriction to a
smaller rational subspace. No finite-dimensionality is needed. -/

namespace Hindman168
open Set Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]

theorem rationalRestrictedKernel_real_span (U : Submodule ℚ E) (F : E →ₗ[ℝ] ℝ)
    (hQ : ∀ u ∈ U, ∃ q : ℚ, F u = (q : ℝ)) :
    span ℝ ((U ⊓ F.ker.restrictScalars ℚ : Submodule ℚ E) : Set E) =
      span ℝ (U : Set E) ⊓ F.ker := by
  apply le_antisymm
  · apply span_le.mpr
    intro u hu
    exact ⟨subset_span hu.1, hu.2⟩
  · by_cases hex : ∃ w ∈ U, F w ≠ 0
    · obtain ⟨w, hw, hFw⟩ := hex
      obtain ⟨qw, hqw⟩ := hQ w hw
      have hqw0 : qw ≠ 0 := by
        intro hz
        apply hFw
        rw [hqw, hz, Rat.cast_zero]
      let P : E →ₗ[ℝ] E := LinearMap.id -
        (LinearMap.toSpanSingleton ℝ E w).comp ((F w)⁻¹ • F)
      have hP (v : E) : P v = v - (F v / F w) • w := by
        simp [P, div_eq_mul_inv, mul_comm]
      have hmap : (span ℝ (U : Set E)).map P ≤
          span ℝ ((U ⊓ F.ker.restrictScalars ℚ : Submodule ℚ E) : Set E) := by
        rw [Submodule.map_span]
        apply span_le.mpr
        rintro _ ⟨v, hv, rfl⟩
        obtain ⟨qv, hqv⟩ := hQ v hv
        have he : P v = v - (qv / qw) • w := by
          rw [hP, hqv, hqw, ← Rat.cast_div, Rat.cast_smul_eq_qsmul]
        rw [he]
        apply subset_span
        refine ⟨U.sub_mem hv (U.smul_mem _ hw), ?_⟩
        change F (v - (qv / qw) • w) = 0
        rw [← Rat.cast_smul_eq_qsmul ℝ, map_sub, map_smul, hqv, hqw]
        norm_cast
        simp [hqw0]
      intro v hv
      apply hmap
      refine ⟨v, hv.1, ?_⟩
      rw [hP]
      have hz : F v = 0 := hv.2
      rw [hz, zero_div, zero_smul, sub_zero]
    · push Not at hex
      have he : U ⊓ F.ker.restrictScalars ℚ = U :=
        inf_eq_left.mpr (fun u hu => hex u hu)
      rw [he]
      exact inf_le_left

theorem rationalRestrictedKernel_rational
    (W : Submodule ℚ E) (S : Submodule ℝ E) (F : E →ₗ[ℝ] ℝ)
    (hS : span ℝ ((S.restrictScalars ℚ ⊓ W : Submodule ℚ E) : Set E) = S)
    (hQ : ∀ w ∈ W, ∃ q : ℚ, F w = (q : ℝ)) :
    span ℝ (((S ⊓ F.ker).restrictScalars ℚ ⊓ W : Submodule ℚ E) : Set E) =
      S ⊓ F.ker := by
  have he : (S ⊓ F.ker).restrictScalars ℚ ⊓ W =
      (S.restrictScalars ℚ ⊓ W) ⊓ F.ker.restrictScalars ℚ := by
    ext x
    exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩
  rw [he, rationalRestrictedKernel_real_span (S.restrictScalars ℚ ⊓ W) F
    (fun w hw => hQ w hw.2), hS]

omit [Module ℚ E] in
theorem restrictedKernel_finrank_lt [FiniteDimensional ℝ E]
    (S : Submodule ℝ E) (F : E →ₗ[ℝ] ℝ) {v : E} (hv : v ∈ S) (hFv : F v ≠ 0) :
    Module.finrank ℝ (S ⊓ F.ker : Submodule ℝ E) < Module.finrank ℝ S := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_iff_le_not_ge.mpr ⟨inf_le_left, ?_⟩
  intro hle
  exact hFv (hle hv).2

end Hindman168
