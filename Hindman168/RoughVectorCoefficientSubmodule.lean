import Hindman168.RoughVectorMvCoefficients
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Quotient.Defs

/-! ACTUAL aggregated vector coefficients belong to an original real
submodule if ALL original natural-grid values do. The algebraic quotient
and scalar polynomial uniqueness prove this without a closure assumption. -/

namespace Hindman168
open Set
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rough_vector_coefficient_mem_of_nat_values (S : Submodule ℝ E)
    (p : RoughVectorMvPolynomial σ E)
    (h : ∀ x : σ → ℕ, roughVectorMvEval p (fun j => (x j : ℝ)) ∈ S) (J : σ →₀ ℕ) :
    roughVectorMvCoefficient p J ∈ S := by
  classical
  apply (Submodule.Quotient.mk_eq_zero S).mp
  apply (Module.forall_dual_apply_eq_zero_iff ℝ (S.mkQ (roughVectorMvCoefficient p J))).mp
  intro φ
  let ell : E →ₗ[ℝ] ℝ := φ.comp S.mkQ
  have hp : roughVectorMvProjection ell p = 0 := by
    apply MvPolynomial.funext_set (fun _ : σ => Set.range (fun n : ℕ => (n : ℝ)))
      (fun _ => Set.infinite_range_of_injective (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℝ))))
    intro x hx
    have hy : ∀ j : σ, ∃ n : ℕ, (n : ℝ) = x j := fun j => hx j (Set.mem_univ j)
    choose n hn using hy
    have he : x = (fun j => (n j : ℝ)) := funext (fun j => (hn j).symm)
    rw [he,roughVectorMvProjection_eval,map_zero]
    change φ (S.mkQ (roughVectorMvEval p (fun j => (n j : ℝ)))) = 0
    have hz : S.mkQ (roughVectorMvEval p (fun j => (n j : ℝ))) = 0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr (h n)
    rw [hz,map_zero]
  change ell (roughVectorMvCoefficient p J) = 0
  rw [rough_vector_coefficient_projection,hp,MvPolynomial.coeff_zero]

theorem rough_vector_weighted_coefficient (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    {p : RoughVectorMvPolynomial σ E} {k : ℕ} (hp : RoughVectorMvWeightedDegree F p k)
    (J : σ →₀ ℕ) : roughVectorMvCoefficient p J ∈ F (J.sum (fun _ n => n)+k) := by
  classical
  induction p with
  | nil => exact (F _).zero_mem
  | cons a p ih =>
      change MvPolynomial.coeff J a.1 • a.2 + roughVectorMvCoefficient p J ∈ F _
      apply (F _).add_mem
      · by_cases he : MvPolynomial.coeff J a.1 = 0
        · rw [he,zero_smul]; exact (F _).zero_mem
        · apply (F _).smul_mem
          exact hF (Nat.add_le_add_right (MvPolynomial.le_totalDegree
            (MvPolynomial.mem_support_iff.mpr he)) k) (hp a List.mem_cons_self)
      · exact ih (fun b hb => hp b (List.mem_cons_of_mem _ hb))

end Hindman168
