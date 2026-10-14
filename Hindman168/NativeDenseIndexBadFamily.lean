import Hindman168.FiniteDenseArithmeticProgression
import Hindman168.RoughIndexProgressionTransport

/-! The original fixed-K density route produces an actual smooth bad family.
K is fixed before every raw source, modulus, box, residue and observable. -/
namespace Hindman168
open scoped Classical
universe u

theorem native_dense_index_bad_family {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℕ, 0 < K ∧ ∀ w N t₀ modulus d : ℕ,
      K ≤ w → K ≤ N → 2*(K : ℝ) ≤ δ*(N : ℝ) →
      ∀ (Scale Z c C B η : ℝ) (L : NNReal)
      (Q : (Option κ → ℝ) → D.G) (p : RoughVectorMvPolynomial (Option κ) D.E),
      RoughVectorMvDegreeLE p d →
      (∀ (z : ℝ) (y : κ → ℝ), roughVectorMvEval p (Option.elim · z y) =
        nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q (Option.elim · z y))) →
      0 < modulus →
      (∀ prime : ℕ, prime.Prime → prime ∣ modulus → prime ≤ w) →
      (∀ n : ℕ, n < N → Scale ≤ (t₀+modulus*n : ℕ) ∧
        (t₀+modulus*n : ℕ) < 2*Scale ∧ (primorial w).Coprime (t₀+modulus*n)) →
      δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n =>
        RoughNativeBadIndex D Q n (t₀+modulus*n) Z c C L B η)).card →
      RoughNativeBadFamily (κ := κ) D H w Scale Z d c C L B η := by
  obtain ⟨K,hK,hAP⟩ := dense_range_bounded_progression H hδ
  refine ⟨K,hK,?_⟩
  intro w N t₀ modulus d hKw hKN htail Scale Z c C B η L Q p hp hlog hmod hsmooth hinterval hd
  let U := (Finset.range N).filter (fun n =>
    RoughNativeBadIndex D Q n (t₀+modulus*n) Z c C L B η)
  obtain ⟨a,b,hb,hbK,hterms⟩ := hAP N hKN htail U
    (fun _ hn => (Finset.mem_filter.mp hn).1) hd
  apply rough_index_progression_bad_family D Q p H w t₀ modulus a b d
    Scale Z c C B η L hp hlog hmod hsmooth hb (hbK.le.trans hKw)
  intro z hz
  obtain ⟨hn,hbad⟩ := Finset.mem_filter.mp (hterms z hz)
  obtain ⟨hlo,hhi,hcop⟩ := hinterval _ (Finset.mem_range.mp hn)
  exact ⟨hlo,hhi,hcop,hbad⟩

end Hindman168
