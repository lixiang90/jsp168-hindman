import Hindman168.NativeRationalCommonLineCharacter
import Hindman168.ScalarMvPolynomialInverse
import Hindman168.ScalarMvLowerDegreeLineRecovery

/-! TRUE dense original basepoint line bounds invoke the PROVED scalar
lower-degree small-value inverse, recovering ALL positive homogeneous line
constants with ONE positive bounded natural multiplier for that direction.
No scalar inverse or missing constant coefficient is assumed. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_rational_line_constant_recovery {s ℓ n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hℓ : 1 ≤ ℓ)
    (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    ∃ B : ℕ, 0 < B ∧ ∀ (p : RoughVectorMvPolynomial (Fin n) D.E),
      RoughVectorMvWeightedDegree L.layer p 0 → ∀ (χ : D.E →L[ℝ] ℝ) (q : Fin n → ℕ)
        (N H Q : ℕ), B ≤ N → 0 < H → (Q : ℝ)/(H : ℝ) ≤ μ/10 →
      μ*((scalarMvIntegerCube (Fin n) N).card : ℝ) ≤
        (((scalarMvIntegerCube (Fin n) N).filter (NativeRationalLineBounds D p ℓ Q H χ q)).card : ℝ) →
      ∃ M : ℕ, 0 < M ∧ M ≤ B^(ℓ+1) ∧ ∀ r : ℕ, 0 < r → r ≤ ℓ →
        ‖(((M : ℝ)*MvPolynomial.coeff 0 (scalarMvLineCoefficient
          (roughVectorMvProjection χ.toLinearMap p) (fun j => (q j : ℝ)) r) : ℝ) : UnitAddCircle)‖ ≤
          ((B^(ℓ+1) : ℕ) : ℝ)*((Q : ℝ)/(H : ℝ)^r) := by
  obtain ⟨B,hB,hSmall⟩ := scalar_mv_polynomial_small_values_inverse n (ℓ-1) μ hμ hμ1
  refine ⟨B,hB,?_⟩
  intro p hp χ q N H Q hBN hH hTol hDense
  have hSucc : ℓ-1+1=ℓ := Nat.sub_add_cancel hℓ
  have hPower : ℓ-1+2=ℓ+1 := by omega
  have hDegree := native_rational_functional_scalar_degree D L p hp χ ℓ
    (by rw [L.terminal]; exact bot_le)
  have hSub : (scalarMvIntegerCube (Fin n) N).filter (NativeRationalLineBounds D p ℓ Q H χ q) ⊆
      (scalarMvIntegerCube (Fin n) N).filter (fun x => ∀ r : ℕ, 0 < r → r ≤ ℓ →
        (H : ℝ)^r*‖((MvPolynomial.eval (fun j => (x j : ℝ))
          (scalarMvLineCoefficient (roughVectorMvProjection χ.toLinearMap p)
            (fun j => (q j : ℝ)) r) : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)) := by
    intro x hx
    obtain ⟨hxN,hBounds⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxN,fun r hr _ => hBounds.1 r hr⟩
  have hCard : (((scalarMvIntegerCube (Fin n) N).filter
      (NativeRationalLineBounds D p ℓ Q H χ q)).card : ℝ) ≤
      (((scalarMvIntegerCube (Fin n) N).filter (fun x => ∀ r : ℕ, 0 < r → r ≤ ℓ →
        (H : ℝ)^r*‖((MvPolynomial.eval (fun j => (x j : ℝ))
          (scalarMvLineCoefficient (roughVectorMvProjection χ.toLinearMap p)
            (fun j => (q j : ℝ)) r) : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hSub
  have hDenseMono := hDense.trans hCard
  have h := scalar_mv_lower_degree_line_recovery (ℓ-1) B hB μ hSmall
    (roughVectorMvProjection χ.toLinearMap p) (by simpa only [hSucc] using hDegree)
    (fun j => (q j : ℝ)) N H 1 hBN hH (Q : ℝ) (Nat.cast_nonneg Q) hTol
    (by simpa only [hSucc,Nat.cast_one,one_mul] using hDenseMono)
  simpa only [hSucc,hPower,Nat.cast_one,one_mul] using h

end Hindman168
