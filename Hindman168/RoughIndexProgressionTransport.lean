import Hindman168.RoughNativeBadFamily
import Hindman168.RoughParameterAffineProjection
import Mathlib.NumberTheory.Primorial

/-! Exact transport of an index progression to an actual native bad family.
The source is changed by literal affine substitution, at every real input.
Smoothness uses the actual bounded positive index step and smooth modulus. -/
namespace Hindman168
open scoped Classical
universe u

theorem rough_index_progression_bad_family {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s)
    (Q : (Option κ → ℝ) → D.G) (p : RoughVectorMvPolynomial (Option κ) D.E)
    (H w t₀ modulus a b d : ℕ) (Scale Z c C B η : ℝ) (L : NNReal)
    (hp : RoughVectorMvDegreeLE p d)
    (hlog : ∀ (z : ℝ) (y : κ → ℝ),
      roughVectorMvEval p (Option.elim · z y) =
        nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q (Option.elim · z y)))
    (hmod : 0 < modulus)
    (hsmooth : ∀ prime : ℕ, prime.Prime → prime ∣ modulus → prime ≤ w)
    (hb : 0 < b) (hbw : b ≤ w)
    (hterms : ∀ z : ℕ, z < H →
      Scale ≤ (t₀ + modulus * (a + b*z) : ℕ) ∧
      (t₀ + modulus * (a + b*z) : ℕ) < 2*Scale ∧
      (primorial w).Coprime (t₀ + modulus * (a + b*z)) ∧
      RoughNativeBadIndex D Q (a+b*z) (t₀ + modulus * (a+b*z)) Z c C L B η) :
    RoughNativeBadFamily (κ := κ) D H w Scale Z d c C L B η := by
  let Q' : (Option κ → ℝ) → D.G := fun x =>
    Q (Option.elim · ((a : ℝ)+(b : ℝ)*x none) (fun j => x (some j)))
  refine ⟨Q', roughParameterAffineSource (a : ℝ) (b : ℝ) p,
    t₀+modulus*a, modulus*b, rough_parameter_affine_degree _ _ hp, ?_,
    Nat.mul_pos hmod hb, ?_, ?_⟩
  · intro z y
    rw [rough_parameter_affine_eval]
    exact hlog _ y
  · intro prime hprime hdiv
    rcases hprime.dvd_mul.mp hdiv with hleft | hright
    · exact hsmooth prime hprime hleft
    · exact (Nat.le_of_dvd hb hright).trans hbw
  · intro z hz
    have he : t₀+modulus*a+(modulus*b)*z=t₀+modulus*(a+b*z) := by ring
    rw [he]
    obtain ⟨hlo,hhi,hcop,hbad⟩ := hterms z hz
    exact ⟨hlo,hhi,hcop,rough_native_bad_index_reparametrize D Q a b z _ Z c C L B η hbad⟩

end Hindman168
