import Hindman168.FinitePiProductLinearApproximation
import Hindman168.BoundedComplexLipschitzObservables

/-! Actual finite coordinate-observer and coefficient budgets from retained
product-span approximants. All list choices and numerical bounds precede
source formulae, original boxes, residues and posterior samples. -/
namespace Hindman168
open scoped BigOperators Classical NNReal

theorem finite_lipschitz_observer_budget (X : Type*) [MetricSpace X] [CompactSpace X]
    (P : Finset C(X,ℂ)) (hP : ∀ F ∈ P, ∃ K : ℝ≥0, LipschitzWith K F) :
    ∃ B : ℝ, ∃ L : ℝ≥0, 0 < B ∧ ∀ F ∈ P, F ∈ boundedComplexLipschitzObservables X B L := by
  have ha : ∀ F : C(X,ℂ), ∃ K : ℝ≥0, F ∈ P → LipschitzWith K F := by
    intro F
    by_cases hf : F ∈ P
    · obtain ⟨K,hK⟩ := hP F hf
      exact ⟨K,fun _ => hK⟩
    · exact ⟨0,fun h => (hf h).elim⟩
  choose k hk using ha
  let B : ℝ := 1+∑ F ∈ P, ‖F‖
  let L : ℝ≥0 := 1+∑ F ∈ P, k F
  refine ⟨B,L,by dsimp only [B]; positivity,?_⟩
  intro F hF
  have hsum := Finset.single_le_sum (f := k) (fun _ _ => (show 0 ≤ _ from zero_le)) hF
  have hle : k F ≤ L := hsum.trans (le_add_of_nonneg_left zero_le_one)
  have hnorm := Finset.single_le_sum (f := fun G : C(X,ℂ) => ‖G‖) (fun G _ => norm_nonneg G) hF
  refine ⟨(hk F hF).weaken hle,?_⟩
  intro x
  exact (F.norm_coe_le_norm x).trans (by dsimp only [B]; linarith)

theorem finite_product_span_common_budgets {ι : Type*} [Fintype ι]
    (X : ι → Type*) [∀ i, MetricSpace (X i)] [∀ i, CompactSpace (X i)]
    (P : Finset C((∀ i, X i),ℂ)) (hP : ∀ G ∈ P, G ∈ finitePiLipschitzProductSpan X) :
    ∃ (terms : C((∀ i, X i),ℂ) → List (ℂ × (∀ i, C(X i,ℂ))))
      (B : ι → ℝ) (L : ι → ℝ≥0) (R : ℝ),
      (∀ i, 0 < B i) ∧ 0 < R ∧
      ∀ G ∈ P, G=finitePiProductLinearCombination X (terms G) ∧
        (∀ t ∈ terms G, ∀ i, t.2 i ∈ boundedComplexLipschitzObservables (X i) (B i) (L i)) ∧
        ((terms G).map (fun t => ‖t.1‖)).sum < R := by
  have ha : ∀ G : C((∀ i, X i),ℂ), ∃ l : List (ℂ × (∀ i, C(X i,ℂ))),
      G ∈ P → (∀ t ∈ l, ∀ i, ∃ K : ℝ≥0, LipschitzWith K (t.2 i)) ∧ G=finitePiProductLinearCombination X l := by
    intro G
    by_cases hg : G ∈ P
    · obtain ⟨l,hl,he⟩ := finite_pi_product_span_list_representation X G (hP G hg)
      exact ⟨l,fun _ => ⟨hl,he⟩⟩
    · exact ⟨[],fun h => (hg h).elim⟩
  choose terms hterms using ha
  let pool : ∀ i, Finset C(X i,ℂ) := fun i => P.biUnion (fun G => ((terms G).map (fun t => t.2 i)).toFinset)
  have hpool (i : ι) (F : C(X i,ℂ)) (hF : F ∈ pool i) : ∃ K : ℝ≥0, LipschitzWith K F := by
    obtain ⟨G,hG,hF⟩ := Finset.mem_biUnion.mp hF
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hF)
    exact (hterms G hG).1 t ht i
  have hb (i : ι) := finite_lipschitz_observer_budget (X i) (pool i) (hpool i)
  choose B L hB hbound using hb
  let size (G : C((∀ i, X i),ℂ)) := ((terms G).map (fun t => ‖t.1‖)).sum
  have hsize (G : C((∀ i, X i),ℂ)) : 0 ≤ size G := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨t,_ht,rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg t.1
  have htotal : 0 ≤ ∑ G ∈ P, size G := Finset.sum_nonneg (fun G _ => hsize G)
  let R : ℝ := 1+∑ G ∈ P, size G
  refine ⟨terms,B,L,R,hB,by dsimp only [R]; linarith,?_⟩
  intro G hG
  refine ⟨(hterms G hG).2,?_,?_⟩
  · intro t ht i
    apply hbound i (t.2 i)
    exact Finset.mem_biUnion.mpr ⟨G,hG,List.mem_toFinset.mpr (List.mem_map.mpr ⟨t,ht,rfl⟩)⟩
  · have hs := Finset.single_le_sum (f := size) (fun G _ => hsize G) hG
    change size G < R
    dsimp only [R]
    linarith

end Hindman168
