import Hindman168.FinitePiLipschitzProducts

/-! Coordinate Lipschitz products separate the FULL compact product cube
space. Stone-Weierstrass therefore approximates EVERY complex continuous
cube test in sup norm by their genuine finite complex linear span. -/
namespace Hindman168
open scoped BigOperators Classical Topology NNReal
variable {ι : Type*} [Fintype ι] (X : ι → Type*) [∀ i, MetricSpace (X i)] [∀ i, CompactSpace (X i)]

omit [∀ i, CompactSpace (X i)] in
theorem finite_pi_complex_product_single (j : ι) (F : C(X j,ℂ)) :
    finitePiComplexProduct X (Pi.mulSingle j F)=F.comp ⟨fun x => x j,continuous_apply j⟩ := by
  ext x
  rw [finite_pi_complex_product_apply]
  have he : (fun i => ((Pi.mulSingle j F : ∀ i, C(X i,ℂ)) i) (x i))=Pi.mulSingle j (F (x j)) := by
    funext i
    by_cases h : i=j
    · subst i; simp only [Pi.mulSingle_eq_same]
    · simp only [Pi.mulSingle_eq_of_ne h,ContinuousMap.one_apply]
  rw [he,Fintype.prod_pi_mulSingle']
  rfl

theorem finite_pi_lipschitz_product_star_subalgebra_separates :
    (finitePiLipschitzProductStarSubalgebra X).SeparatesPoints := by
  intro x y hxy
  obtain ⟨j,hj⟩ : ∃ j, x j ≠ y j := by
    by_contra hn
    apply hxy
    funext j
    by_contra h
    exact hn ⟨j,h⟩
  obtain ⟨f,⟨F,hF,rfl⟩,hneq⟩ := (compact_lipschitz_star_subalgebra_separates (X j)) hj
  change ∃ K : ℝ≥0, LipschitzWith K F at hF
  let P := finitePiComplexProduct X (Pi.mulSingle j F)
  have hP : P ∈ finitePiLipschitzProductStarSubalgebra X := by
    apply Submodule.subset_span
    refine ⟨Pi.mulSingle j F,?_,rfl⟩
    intro i
    by_cases h : i=j
    · subst i
      simpa only [Pi.mulSingle_eq_same] using hF
    · rw [Pi.mulSingle_eq_of_ne h]
      exact ⟨0,LipschitzWith.of_dist_le_mul (fun _ _ => by simp)⟩
  refine ⟨(P : (∀ i, X i) → ℂ),⟨P,hP,rfl⟩,?_⟩
  have he := finite_pi_complex_product_single X j F
  have hx := congrArg (fun p : C((∀ i, X i),ℂ) => p x) he
  have hy := congrArg (fun p : C((∀ i, X i),ℂ) => p y) he
  intro h
  exact hneq (hx.symm.trans (h.trans hy))

theorem finite_pi_lipschitz_product_span_closure :
    closure (finitePiLipschitzProductSpan X : Set C((∀ i, X i),ℂ))=Set.univ := by
  have hh := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (finitePiLipschitzProductStarSubalgebra X) (finite_pi_lipschitz_product_star_subalgebra_separates X)
  have hc := congrArg (fun A : StarSubalgebra ℂ C((∀ i, X i),ℂ) => (A : Set C((∀ i, X i),ℂ))) hh
  exact hc

theorem finite_pi_lipschitz_product_uniform_approximation (F : C((∀ i, X i),ℂ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ G ∈ finitePiLipschitzProductSpan X, ‖F-G‖ < ε := by
  have hf : F ∈ closure (finitePiLipschitzProductSpan X : Set C((∀ i, X i),ℂ)) := by
    rw [finite_pi_lipschitz_product_span_closure]; trivial
  obtain ⟨G,hG,hclose⟩ := Metric.mem_closure_iff.mp hf ε hε
  exact ⟨G,hG,by simpa only [dist_eq_norm] using hclose⟩

end Hindman168
