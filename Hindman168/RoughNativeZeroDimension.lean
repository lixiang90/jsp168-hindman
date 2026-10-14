import Hindman168.RoughNativeBadFamily
import Hindman168.FiniteCountableExpectations

namespace Hindman168
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_zero_dimension_no_bad_index {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (hdim : Module.finrank ℝ D.E = 0)
    (Q : (Option κ → ℝ) → D.G) (z t : ℕ) (Z c C : ℝ) (L : NNReal) (B η : ℝ)
    (hη : 0 < η) : ¬ RoughNativeBadIndex D Q z t Z c C L B η := by
  letI : Subsingleton D.E := Module.finrank_zero_iff.mp hdim
  letI : Subsingleton D.G := ⟨fun g h => by
    rw [← nativeLieExponential_globalLogarithm (E := D.E) (I := D.I) g,
      ← nativeLieExponential_globalLogarithm (E := D.E) (I := D.I) h]
    exact congrArg (fun v : D.E => nativeLieExponential (I := D.I) (G := D.G) v)
      (Subsingleton.elim _ _)⟩
  letI : Subsingleton (D.G ⧸ D.Γ) := ⟨fun x y => Quotient.inductionOn₂ x y
    (fun g h => congrArg (QuotientGroup.mk : D.G → D.G ⧸ D.Γ) (Subsingleton.elim g h))⟩
  intro h
  obtain ⟨lo, hi, v, F, _, _, _, hstep, hfull, hbad⟩ := h
  have hc : (fun y : κ → ℤ => F (QuotientGroup.mk
      (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ)))))) =
      (fun _ => F (QuotientGroup.mk (1 : D.G))) := by
    funext y
    exact congrArg F (Subsingleton.elim _ _)
  rw [hc, FiniteMass.expectation_const, FiniteMass.expectation_const,
    FiniteMass.uniformFinsetMass_total _ hstep,
    FiniteMass.uniformFinsetMass_total _ hfull] at hbad
  simp only [one_mul, sub_self, abs_zero] at hbad
  exact (not_lt_of_ge hη.le) hbad

theorem rough_native_zero_dimension_no_bad_family {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (hdim : Module.finrank ℝ D.E = 0)
    (H w : ℕ) (Scale Z : ℝ) (d : ℕ) (c C : ℝ) (L : NNReal) (B η : ℝ)
    (hH : 0 < H) (hη : 0 < η) :
    ¬ RoughNativeBadFamily (κ := κ) D H w Scale Z d c C L B η := by
  rintro ⟨Q, _, t, diff, _, _, _, _, hbad⟩
  exact rough_native_zero_dimension_no_bad_index D hdim Q 0 (t+diff*0) Z c C L B η hη
    (hbad 0 hH).2.2.2

end Hindman168
