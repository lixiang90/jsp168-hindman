import Hindman168.NilCornerReconstruction

/-! One uniform finite coefficient bound for the paper's fixed finite
list of compact cube spaces/nilmanifolds, allowing different ambient
spaces and different observable families at the different entries. -/

namespace Hindman168
open scoped BigOperators Classical
open NNReal

theorem compactCorner_finite_boundedLipschitz_recipes {σ ι : Type*}
    [Fintype σ] [Fintype ι] (X : σ → Type*)
    [∀ i, MetricSpace (X i)] [∀ i, CompactSpace (X i)]
    (K : ∀ i, Set (Option ι → X i))
    (hcompact : ∀ i, IsCompact (K i)) (hunique : ∀ i, CornerUnique (K i))
    (A : ∀ i, Set C(X i, ℝ)) (B : σ → ℝ) (L : σ → ℝ≥0)
    (hB : ∀ i, ∀ f ∈ A i, ∀ x, |f x| ≤ B i)
    (hL : ∀ i, ∀ f ∈ A i, LipschitzWith (L i) f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ recipes : ∀ i, Finset (CornerProductRecipe ι (X i)), ∃ C : ℝ, 0 ≤ C ∧
      (∀ i, ∀ r ∈ recipes i, CornerProductRecipe.Bounded r ∧ r.coefficientMass ≤ C) ∧
      (∀ i, ∀ f ∈ A i, ∃ r ∈ recipes i, ∀ c ∈ K i,
        |r.value (cornerDelete c) - f (c none)| < ε) := by
  have h : ∀ i, ∃ recipes : Finset (CornerProductRecipe ι (X i)), ∃ C : ℝ, 0 ≤ C ∧
      (∀ r ∈ recipes, CornerProductRecipe.Bounded r ∧ r.coefficientMass ≤ C) ∧
      (∀ f ∈ A i, ∃ r ∈ recipes, ∀ c ∈ K i,
        |r.value (cornerDelete c) - f (c none)| < ε) := by
    intro i
    exact compactCorner_boundedLipschitz_recipes (K i) (hcompact i) (hunique i)
      (A i) (B i) (L i) (hB i) (hL i) ε hε
  choose recipes bound hnonneg hbounded happrox using h
  refine ⟨recipes, ∑ i, bound i, Finset.sum_nonneg (fun i _ => hnonneg i), ?_, happrox⟩
  intro i r hr
  exact ⟨(hbounded i r hr).1, (hbounded i r hr).2.trans
    (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i))⟩

end Hindman168
