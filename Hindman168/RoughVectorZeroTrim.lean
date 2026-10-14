import Hindman168.RoughVectorWeightedDegree

namespace Hindman168
open scoped Classical
variable {σ E : Type*}

noncomputable def roughVectorMvZeroTrim [Zero E] (p : RoughVectorMvPolynomial σ E) :
    RoughVectorMvPolynomial σ E := p.filter (fun a => a.2 ≠ 0)

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rough_vector_zero_trim_eval (p : RoughVectorMvPolynomial σ E) (x : σ → ℝ) :
    roughVectorMvEval (roughVectorMvZeroTrim p) x = roughVectorMvEval p x := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      by_cases ha : a.2 = 0
      · simp only [roughVectorMvZeroTrim, List.filter_cons, ha, ne_eq, not_true_eq_false,
          decide_false, Bool.false_eq_true, ↓reduceIte]
        change roughVectorMvEval (roughVectorMvZeroTrim p) x =
          MvPolynomial.eval x a.1 • a.2+roughVectorMvEval p x
        rw [ih, ha, smul_zero, zero_add]
      · simp only [roughVectorMvZeroTrim, List.filter_cons, ha, ne_eq, not_false_eq_true,
          decide_true, ↓reduceIte]
        change MvPolynomial.eval x a.1 • a.2+roughVectorMvEval (roughVectorMvZeroTrim p) x =
          MvPolynomial.eval x a.1 • a.2+roughVectorMvEval p x
        rw [ih]

theorem rough_vector_zero_trim_weighted (F : ℕ → Submodule ℝ E)
    {p : RoughVectorMvPolynomial σ E} {k : ℕ} (hp : RoughVectorMvWeightedDegree F p k) :
    RoughVectorMvWeightedDegree F (roughVectorMvZeroTrim p) k :=
  fun a ha => hp a (List.mem_of_mem_filter ha)

theorem rough_vector_zero_trim_degree (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    {p : RoughVectorMvPolynomial σ E} {k L : ℕ}
    (hp : RoughVectorMvWeightedDegree F p k) (hL : F (L+1) = ⊥) :
    RoughVectorMvDegreeLE (roughVectorMvZeroTrim p) (L-k) := by
  intro a ha
  have hm := List.mem_filter.mp ha
  have hn : a.2 ≠ 0 := of_decide_eq_true hm.2
  have hw := hp a hm.1
  by_contra! hd
  have hi : L+1 ≤ a.1.totalDegree+k := by omega
  have hz := hF hi hw
  rw [hL, Submodule.mem_bot] at hz
  exact hn hz

end Hindman168
