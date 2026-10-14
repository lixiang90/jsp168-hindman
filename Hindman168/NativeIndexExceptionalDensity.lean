import Hindman168.NativeDenseIndexBadFamily
import Hindman168.NativeNoLongBadFamily

/-! Uniform exceptional-density conclusion on exact index intervals.
The length threshold and eventual scale threshold precede ALL raw sources.
Residue-interval identification is supplied separately, not assumed solved. -/
namespace Hindman168
open Filter
open scoped Classical
universe u

def NativeIndexExceptionalBound {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (n d w N₀ : ℕ) (Scale Z c C B η δ : ℝ) (L : NNReal) : Prop :=
  ∀ N t₀ modulus : ℕ, N₀ ≤ N →
    ∀ (Q : (Option (Fin n) → ℝ) → D.G)
      (p : RoughVectorMvPolynomial (Option (Fin n)) D.E),
    RoughVectorMvDegreeLE p d →
    (∀ (z : ℝ) (y : Fin n → ℝ), roughVectorMvEval p (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q (Option.elim · z y))) →
    0 < modulus →
    (∀ prime : ℕ, prime.Prime → prime ∣ modulus → prime ≤ w) →
    (∀ j : ℕ, j < N → Scale ≤ (t₀+modulus*j : ℕ) ∧
      (t₀+modulus*j : ℕ) < 2*Scale ∧ (primorial w).Coprime (t₀+modulus*j)) →
    (((Finset.range N).filter (fun j =>
      RoughNativeBadIndex D Q j (t₀+modulus*j) Z c C L B η)).card : ℝ) < δ*(N : ℝ)

theorem native_index_exceptional_density {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (n d : ℕ) (c C B η : ℝ) (L : NNReal)
    (hc : 0 < c) (hC : 1 ≤ C) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hScale : Tendsto Scale atTop atTop)
    (hg : ∀ a : ℝ, 0 < a → Tendsto (fun w => Z w/(Scale w)^a) atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ᶠ w in atTop,
      NativeIndexExceptionalBound D n d w N₀ (Scale w) (Z w) c C B η δ L := by
  obtain ⟨H,hH,hNoBad⟩ := native_no_long_bad_family D n d c C B η L
    hc hC hB hη Scale Z hScale hg
  obtain ⟨K,hK,hDense⟩ := native_dense_index_bad_family (κ := Fin n) D H hδ
  let N₀ := max K ⌈2*(K : ℝ)/δ⌉₊
  refine ⟨N₀,lt_of_lt_of_le hK (le_max_left _ _),?_⟩
  filter_upwards [hNoBad,eventually_ge_atTop K] with w hno hKw
  intro N t₀ modulus hN Q p hp hlog hmod hsmooth hinterval
  have hKN : K ≤ N := (le_max_left _ _).trans hN
  have hceil : ⌈2*(K : ℝ)/δ⌉₊ ≤ N := (le_max_right _ _).trans hN
  have htail : 2*(K : ℝ) ≤ δ*(N : ℝ) := by
    have hratio : 2*(K : ℝ)/δ ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hceil)
    nlinarith [(div_le_iff₀ hδ).mp hratio]
  by_contra! hden
  exact hno (hDense w N t₀ modulus d hKw hKN htail
    (Scale w) (Z w) c C B η L Q p hp hlog hmod hsmooth hinterval hden)

end Hindman168
