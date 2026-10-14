import Hindman168.RoughVectorMvPolynomial
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace Hindman168
open Module
open scoped BigOperators

variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roughVectorMvFromBasis {n : ℕ} (b : Basis (Fin n) ℝ E)
    (p : Fin n → MvPolynomial σ ℝ) : RoughVectorMvPolynomial σ E :=
  List.ofFn (fun i => (p i, b i))

theorem roughVectorMvFromBasis_eval {n : ℕ} (b : Basis (Fin n) ℝ E)
    (p : Fin n → MvPolynomial σ ℝ) (x : σ → ℝ) :
    roughVectorMvEval (roughVectorMvFromBasis b p) x = ∑ i, MvPolynomial.eval x (p i) • b i := by
  simp [roughVectorMvFromBasis, roughVectorMvEval, List.map_ofFn, List.sum_ofFn]

theorem roughVectorMvFromBasis_degree {n d : ℕ} (b : Basis (Fin n) ℝ E)
    (p : Fin n → MvPolynomial σ ℝ) (hp : ∀ i, (p i).totalDegree ≤ d) :
    RoughVectorMvDegreeLE (roughVectorMvFromBasis b p) d := by
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact hp i

theorem roughVectorMvFromBasis_represents {n : ℕ} (b : Basis (Fin n) ℝ E)
    (p : Fin n → MvPolynomial σ ℝ) (f : (σ → ℝ) → E)
    (hp : ∀ x i, MvPolynomial.eval x (p i) = b.repr (f x) i) (x : σ → ℝ) :
    roughVectorMvEval (roughVectorMvFromBasis b p) x = f x := by
  rw [roughVectorMvFromBasis_eval]
  simp_rw [hp x]
  exact b.sum_repr (f x)

theorem roughVectorMv_subspace_coordinate (S : Submodule ℝ E)
    (p : RoughVectorMvPolynomial σ E) (d : ℕ) (hd : RoughVectorMvDegreeLE p d)
    (hm : ∀ x, roughVectorMvEval p x ∈ S) (ell : S →ₗ[ℝ] ℝ) :
    ∃ q : MvPolynomial σ ℝ, q.totalDegree ≤ d ∧
      ∀ x, MvPolynomial.eval x q = ell ⟨roughVectorMvEval p x, hm x⟩ := by
  obtain ⟨L, hL⟩ := ell.exists_extend
  refine ⟨roughVectorMvProjection L p, roughVectorMvProjection_degree L hd, ?_⟩
  intro x
  rw [roughVectorMvProjection_eval]
  exact LinearMap.congr_fun hL ⟨roughVectorMvEval p x, hm x⟩

end Hindman168
