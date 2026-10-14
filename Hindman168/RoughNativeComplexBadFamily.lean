import Hindman168.RoughNativeBadFamily
import Hindman168.RoughNativeComplexBadIndex
import Hindman168.RoughNativeZeroDimension

namespace Hindman168
open scoped Classical
universe u

def RoughNativeComplexBadFamily {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H w : ℕ) (Scale Z : ℝ)
    (d : ℕ) (c C : ℝ) (L : NNReal) (B η : ℝ) : Prop :=
  ∃ (Q : (Option κ → ℝ) → D.G) (p : RoughVectorMvPolynomial (Option κ) D.E)
    (t diff : ℕ),
    RoughVectorMvDegreeLE p d ∧
    (∀ (z : ℝ) (y : κ → ℝ), roughVectorMvEval p (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q (Option.elim · z y))) ∧
    0 < diff ∧ (∀ prime : ℕ, prime.Prime → prime ∣ diff → prime ≤ w) ∧
    ∀ z : ℕ, z < H → Scale ≤ (t+diff*z : ℕ) ∧ (t+diff*z : ℕ) < 2*Scale ∧
      (primorial w).Coprime (t+diff*z) ∧
      RoughNativeComplexBadIndex D Q z (t+diff*z) Z c C L B η

theorem rough_native_complex_bad_family_length_mono {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) {H H' w : ℕ} {Scale Z : ℝ}
    {d : ℕ} {c C : ℝ} {L : NNReal} {B η : ℝ} (hH : H ≤ H')
    (h : RoughNativeComplexBadFamily (κ := κ) D H' w Scale Z d c C L B η) :
    RoughNativeComplexBadFamily (κ := κ) D H w Scale Z d c C L B η := by
  obtain ⟨Q, p, t, diff, hd, hp, hdiff, hsmooth, hbad⟩ := h
  exact ⟨Q, p, t, diff, hd, hp, hdiff, hsmooth, fun z hz => hbad z (hz.trans_le hH)⟩

theorem rough_native_complex_bad_family_real {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H w : ℕ) (Scale Z : ℝ)
    (d : ℕ) (c C : ℝ) (L : NNReal) (B η : ℝ)
    (h : RoughNativeComplexBadFamily (κ := κ) D H w Scale Z d c C L B η) :
    RoughNativeBadFamily (κ := κ) D H w Scale Z d c C L B (η/2) := by
  obtain ⟨Q, p, t, diff, hd, hp, hdiff, hsmooth, hbad⟩ := h
  refine ⟨Q, p, t, diff, hd, hp, hdiff, hsmooth, ?_⟩
  intro z hz
  obtain ⟨hlo, hhi, hrough, hb⟩ := hbad z hz
  exact ⟨hlo, hhi, hrough, rough_native_complex_bad_index_real D Q z (t+diff*z) Z c C L B η hb⟩

theorem rough_native_zero_dimension_no_complex_bad_index {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (hdim : Module.finrank ℝ D.E = 0)
    (Q : (Option κ → ℝ) → D.G) (z t : ℕ) (Z c C : ℝ) (L : NNReal) (B η : ℝ)
    (hη : 0 < η) : ¬ RoughNativeComplexBadIndex D Q z t Z c C L B η := by
  intro h
  exact rough_native_zero_dimension_no_bad_index D hdim Q z t Z c C L B (η/2)
    (by positivity) (rough_native_complex_bad_index_real D Q z t Z c C L B η h)

theorem rough_native_zero_dimension_no_complex_bad_family {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (hdim : Module.finrank ℝ D.E = 0)
    (H w : ℕ) (Scale Z : ℝ) (d : ℕ) (c C : ℝ) (L : NNReal) (B η : ℝ)
    (hH : 0 < H) (hη : 0 < η) :
    ¬ RoughNativeComplexBadFamily (κ := κ) D H w Scale Z d c C L B η := by
  intro h
  exact rough_native_zero_dimension_no_bad_family D hdim H w Scale Z d c C L B (η/2)
    hH (by positivity) (rough_native_complex_bad_family_real D H w Scale Z d c C L B η h)

end Hindman168
