import Hindman168.NativePieceRecipes

/-! Clipping the entire observable preserves the exact unit-range
sequence, quotient, translating elements and uniform bounds. -/

namespace Hindman168
open NNReal
open scoped Topology
universe u

theorem unitIntervalClip_abs_le (t : ℝ) : |unitIntervalClip t| ≤ |t| := by
  have h := unitIntervalClip_lipschitz.dist_le_mul t 0
  have hz : unitIntervalClip (0 : ℝ) = 0 := by norm_num [unitIntervalClip]
  simpa only [Real.dist_eq, hz, sub_zero, NNReal.coe_one, one_mul] using h

theorem piecewise_unit_observables {G : Type*} [Group G]
    (Γ : Subgroup G) [MetricSpace (G ⧸ Γ)] {N : ℕ}
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (f : ℕ → ℤ → ℝ)
    (hunit : ∀ w y, 0 ≤ f w y ∧ f w y ≤ 1)
    (obs : ℕ → (ℤ × ℤ) → C(G ⧸ Γ, ℝ)) (g x : ℕ → (ℤ × ℤ) → G)
    (B : ℝ) (Lip : ℝ≥0) (hb : ∀ w p z, |obs w p z| ≤ B)
    (hl : ∀ w p, LipschitzWith Lip (obs w p))
    (he : f = piecewiseLinearNilsequence Γ F gap obs g x) :
    ∃ obs' : ℕ → (ℤ × ℤ) → C(G ⧸ Γ, ℝ),
      (∀ w p z, 0 ≤ obs' w p z ∧ obs' w p z ≤ 1) ∧
      (∀ w p z, |obs' w p z| ≤ B) ∧
      (∀ w p, LipschitzWith Lip (obs' w p)) ∧
      f = piecewiseLinearNilsequence Γ F gap obs' g x := by
  let ψ : C(ℝ, ℝ) := ⟨unitIntervalClip, unitIntervalClip_lipschitz.continuous⟩
  refine ⟨fun w p => ψ.comp (obs w p), ?_, ?_, ?_, ?_⟩
  · exact fun w p z => unitIntervalClip_bounds (obs w p z)
  · exact fun w p z => (unitIntervalClip_abs_le (obs w p z)).trans (hb w p z)
  · intro w p
    change LipschitzWith Lip (unitIntervalClip ∘ (obs w p))
    simpa only [one_mul] using unitIntervalClip_lipschitz.comp (hl w p)
  · have hf : f = fun w y => unitIntervalClip (f w y) := by
      funext w y
      simp only [unitIntervalClip, min_eq_right (hunit w y).2, max_eq_right (hunit w y).1]
    calc
      f = (fun w y => unitIntervalClip (f w y)) := hf
      _ = piecewiseLinearNilsequence Γ F gap (fun w p => ψ.comp (obs w p)) g x := by
        rw [he]
        rfl

theorem native_piece_on_unit_observables {s N : ℕ} (D : NativeNilmanifoldData.{u} s)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (f : ℕ → ℤ → ℝ)
    (hf : nativePieceOn D F gap f) (hunit : ∀ w y, 0 ≤ f w y ∧ f w y ≤ 1) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ (obs : ℕ → (ℤ × ℤ) → C(D.G ⧸ D.Γ, ℝ))
      (g x : ℕ → (ℤ × ℤ) → D.G) (Lip : ℝ≥0),
      (∀ w p z, 0 ≤ obs w p z ∧ obs w p z ≤ 1) ∧
      (∀ w p, LipschitzWith Lip (obs w p)) ∧
      f = piecewiseLinearNilsequence D.Γ F gap obs g x := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨obs, g, x, B, Lip, _, hb, hl, he⟩ := hf
  obtain ⟨obs', hunit', _, hl', he'⟩ :=
    piecewise_unit_observables D.Γ F gap f hunit obs g x B Lip hb hl he
  exact ⟨obs', g, x, Lip, hunit', hl', he'⟩

end Hindman168
