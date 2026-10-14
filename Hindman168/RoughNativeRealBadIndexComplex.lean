import Hindman168.RoughNativeComplexBadIndex

/-! A real original bad pair embeds in the complex formulation with EXACT
same discrepancy, Lipschitz/norm bounds, geometry and original samples. -/
namespace Hindman168
open scoped Classical BigOperators
universe u

theorem finite_mass_complex_expectation_real {α : Type*} (μ : FiniteMass.Mass α) (f : α → ℝ) :
    FiniteMass.complexExpectation μ (fun x => (f x : ℂ)) = (FiniteMass.expectation μ f : ℂ) := by
  unfold FiniteMass.complexExpectation FiniteMass.expectation Finsupp.sum
  simp only [Complex.ofReal_sum,Complex.ofReal_mul]

theorem rough_native_real_bad_index_complex {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (z t : ℕ) (Z c C : ℝ) (L : NNReal) (B η : ℝ)
    (h : RoughNativeBadIndex D Q z t Z c C L B η) :
    RoughNativeComplexBadIndex D Q z t Z c C L B η := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨lo,hi,v,F,hL,hB,hBox,hStep,hFull,hBad⟩ := h
  have hLip : LipschitzWith L (fun x => (F x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact hL.dist_le_mul x y
  refine ⟨lo,hi,v,(fun x => (F x : ℂ)),hLip,?_,hBox,hStep,hFull,?_⟩
  · intro x
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hB x
  · rw [finite_mass_complex_expectation_real,finite_mass_complex_expectation_real,
      ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact hBad

end Hindman168
