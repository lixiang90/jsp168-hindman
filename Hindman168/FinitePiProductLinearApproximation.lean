import Hindman168.FinitePiLipschitzProductDensity

/-! Finite product-span approximants expose their actual coefficient and
original coordinate-observer lists. A compact COMPLETE cube test family
admits ONE finite list before all sampling/source data. -/
namespace Hindman168
open scoped BigOperators Classical Topology NNReal
variable {ι : Type*} [Fintype ι] (X : ι → Type*) [∀ i, MetricSpace (X i)] [∀ i, CompactSpace (X i)]

noncomputable def finitePiProductLinearCombination
    (terms : List (ℂ × (∀ i, C(X i,ℂ)))) : C((∀ i, X i),ℂ) :=
  (terms.map (fun t => t.1 • finitePiComplexProduct X t.2)).sum

omit [∀ i, CompactSpace (X i)] in
theorem finite_pi_product_linear_combination_append
    (l m : List (ℂ × (∀ i, C(X i,ℂ)))) :
    finitePiProductLinearCombination X (l++m)=
      finitePiProductLinearCombination X l+finitePiProductLinearCombination X m := by
  simp only [finitePiProductLinearCombination,List.map_append,List.sum_append]

omit [∀ i, CompactSpace (X i)] in
theorem finite_pi_product_linear_combination_smul (c : ℂ)
    (l : List (ℂ × (∀ i, C(X i,ℂ)))) :
    finitePiProductLinearCombination X (l.map (fun t => (c*t.1,t.2)))=
      c • finitePiProductLinearCombination X l := by
  simp only [finitePiProductLinearCombination,List.map_map,List.smul_sum]
  congr 1
  congr 1
  funext t
  exact mul_smul c t.1 (finitePiComplexProduct X t.2)

omit [∀ i, CompactSpace (X i)] in
theorem finite_pi_product_span_list_representation (F : C((∀ i, X i),ℂ))
    (hF : F ∈ finitePiLipschitzProductSpan X) :
    ∃ l : List (ℂ × (∀ i, C(X i,ℂ))),
      (∀ t ∈ l, ∀ i, ∃ K : ℝ≥0, LipschitzWith K (t.2 i)) ∧ F=finitePiProductLinearCombination X l := by
  induction hF using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨F,hF,rfl⟩ := hf
    refine ⟨[(1,F)],?_,?_⟩
    · intro t ht
      have he : t=(1,F) := List.mem_singleton.mp ht
      subst t
      exact hF
    · simp only [finitePiProductLinearCombination,List.map_singleton,List.sum_singleton,one_smul]
  | zero => exact ⟨[],by simp,by simp only [finitePiProductLinearCombination,List.map_nil,List.sum_nil]⟩
  | add f g hf hg ihf ihg =>
    obtain ⟨l,hl,hfl⟩ := ihf
    obtain ⟨m,hm,hgm⟩ := ihg
    refine ⟨l++m,?_,?_⟩
    · intro t ht
      exact (List.mem_append.mp ht).elim (hl t) (hm t)
    · rw [finite_pi_product_linear_combination_append,hfl,hgm]
  | smul c f hf ih =>
    obtain ⟨l,hl,hfl⟩ := ih
    refine ⟨l.map (fun t => (c*t.1,t.2)),?_,?_⟩
    · intro t ht
      obtain ⟨oldTerm,hOld,hEq⟩ := List.mem_map.mp ht
      rw [←hEq]
      exact hl oldTerm hOld
    · rw [finite_pi_product_linear_combination_smul,hfl]

theorem finite_pi_product_linear_uniform_approximation (F : C((∀ i, X i),ℂ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ l : List (ℂ × (∀ i, C(X i,ℂ))),
      (∀ t ∈ l, ∀ i, ∃ K : ℝ≥0, LipschitzWith K (t.2 i)) ∧
      ‖F-finitePiProductLinearCombination X l‖ < ε := by
  obtain ⟨G,hG,hclose⟩ := finite_pi_lipschitz_product_uniform_approximation X F ε hε
  obtain ⟨l,hl,rfl⟩ := finite_pi_product_span_list_representation X G hG
  exact ⟨l,hl,hclose⟩

theorem compact_family_finite_pi_product_span_approximation
    (H : Set C((∀ i, X i),ℂ)) (hH : IsCompact H) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Finset C((∀ i, X i),ℂ),
      (∀ G ∈ P, G ∈ finitePiLipschitzProductSpan X) ∧
      ∀ F ∈ H, ∃ G ∈ P, ‖F-G‖ < ε := by
  have ha : ∀ F : C((∀ i, X i),ℂ), ∃ G ∈ finitePiLipschitzProductSpan X, ‖F-G‖ < ε/2 :=
    fun F => finite_pi_lipschitz_product_uniform_approximation X F (ε/2) (by positivity)
  choose G hG hClose using ha
  obtain ⟨t,_,ht,hcover⟩ := hH.finite_cover_balls (by positivity : 0 < ε/2)
  refine ⟨ht.toFinset.image G,?_,?_⟩
  · intro K hK
    obtain ⟨F,_,rfl⟩ := Finset.mem_image.mp hK
    exact hG F
  · intro F hF
    obtain ⟨K,hK⟩ := Set.mem_iUnion.mp (hcover hF)
    obtain ⟨hKt,hBall⟩ := Set.mem_iUnion.mp hK
    refine ⟨G K,Finset.mem_image.mpr ⟨K,ht.mem_toFinset.mpr hKt,rfl⟩,?_⟩
    have hd : ‖F-K‖ < ε/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hBall
    have htri := dist_triangle F K (G K)
    simp only [dist_eq_norm] at htri
    linarith only [hd,hClose K,htri]

end Hindman168
