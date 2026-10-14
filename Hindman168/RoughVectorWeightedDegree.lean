import Hindman168.RoughVectorMvPolynomial

/-! A termwise sufficient weighted coefficient condition for actual vector
polynomials. It is preserved by scalar linear operations and by brackets
that add filtration weights. No polynomial group difference is inferred
merely from ordinary degree. -/

namespace Hindman168
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def RoughVectorMvWeightedDegree (F : ℕ → Submodule ℝ E)
    (p : RoughVectorMvPolynomial σ E) (k : ℕ) : Prop :=
  ∀ a ∈ p, a.2 ∈ F (a.1.totalDegree+k)

theorem rough_vector_weighted_append (F : ℕ → Submodule ℝ E)
    {p q : RoughVectorMvPolynomial σ E} {k : ℕ}
    (hp : RoughVectorMvWeightedDegree F p k) (hq : RoughVectorMvWeightedDegree F q k) :
    RoughVectorMvWeightedDegree F (p++q) k :=
  fun a ha => (List.mem_append.mp ha).elim (hp a) (hq a)

theorem rough_vector_weighted_scale (F : ℕ → Submodule ℝ E) (r : ℝ)
    {p : RoughVectorMvPolynomial σ E} {k : ℕ} (hp : RoughVectorMvWeightedDegree F p k) :
    RoughVectorMvWeightedDegree F (roughVectorMvScale r p) k := by
  rintro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact (F (b.1.totalDegree+k)).smul_mem r (hp b hb)

theorem rough_vector_weighted_bilinear (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))
    {p q : RoughVectorMvPolynomial σ E} {k l : ℕ}
    (hp : RoughVectorMvWeightedDegree F p k) (hq : RoughVectorMvWeightedDegree F q l) :
    RoughVectorMvWeightedDegree F (roughVectorMvBilinear B p q) (k+l) := by
  rintro a ha
  obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  apply hF _ (hB _ _ _ _ (hp b hb) (hq c hc))
  have hd := MvPolynomial.totalDegree_mul b.1 c.1
  dsimp
  omega

theorem rough_vector_weighted_eval (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    {p : RoughVectorMvPolynomial σ E} {k : ℕ} (hp : RoughVectorMvWeightedDegree F p k)
    (x : σ → ℝ) : roughVectorMvEval p x ∈ F k := by
  induction p with
  | nil => exact (F k).zero_mem
  | cons a p ih =>
      change MvPolynomial.eval x a.1 • a.2 + roughVectorMvEval p x ∈ F k
      apply (F k).add_mem
      · exact (F k).smul_mem _
          (hF (Nat.le_add_left k a.1.totalDegree) (hp a List.mem_cons_self))
      · exact ih (fun b hb => hp b (List.mem_cons_of_mem _ hb))

end Hindman168
