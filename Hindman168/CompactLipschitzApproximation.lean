import Hindman168.CompactLipschitzAlgebra

/-! Actual spatial Lipschitz functions are uniformly dense on ANY fixed
compact metric space. A COMPACT family admits one finite approximant list. -/

namespace Hindman168
open scoped Topology Classical NNReal

theorem compact_lipschitz_uniform_approximation (X : Type*) [MetricSpace X] [CompactSpace X]
    (F : C(X, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ G : C(X, ℂ), (∃ L : ℝ≥0, LipschitzWith L G) ∧ ‖F-G‖ < ε := by
  have he := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (compactLipschitzStarSubalgebra X) (compact_lipschitz_star_subalgebra_separates X)
  have hf : F ∈ (compactLipschitzStarSubalgebra X).topologicalClosure := by rw [he]; trivial
  change F ∈ closure ((compactLipschitzStarSubalgebra X) : Set C(X, ℂ)) at hf
  obtain ⟨G, hG, hclose⟩ := Metric.mem_closure_iff.mp hf ε hε
  exact ⟨G, hG, by simpa only [dist_eq_norm] using hclose⟩

theorem compact_family_finite_lipschitz_approximation (X : Type*) [MetricSpace X] [CompactSpace X]
    (H : Set C(X, ℂ)) (hH : IsCompact H) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Finset C(X, ℂ),
      (∀ G ∈ P, ∃ L : ℝ≥0, LipschitzWith L G) ∧
      ∀ F ∈ H, ∃ G ∈ P, ‖F-G‖ < ε := by
  have ha : ∀ F : C(X, ℂ), ∃ G : C(X, ℂ), (∃ L : ℝ≥0, LipschitzWith L G) ∧ ‖F-G‖ < ε/2 :=
    fun F => compact_lipschitz_uniform_approximation X F (ε/2) (by positivity)
  choose G hLip hClose using ha
  obtain ⟨t, _, ht, hcover⟩ := hH.finite_cover_balls (by positivity : 0 < ε/2)
  refine ⟨ht.toFinset.image G, ?_, ?_⟩
  · intro K hK
    obtain ⟨F, _, rfl⟩ := Finset.mem_image.mp hK
    exact hLip F
  · intro F hF
    obtain ⟨K, hK⟩ := Set.mem_iUnion.mp (hcover hF)
    obtain ⟨hKt, hBall⟩ := Set.mem_iUnion.mp hK
    refine ⟨G K, Finset.mem_image.mpr ⟨K, ht.mem_toFinset.mpr hKt, rfl⟩, ?_⟩
    have hd : ‖F-K‖ < ε/2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hBall
    have htri := dist_triangle F K (G K)
    simp only [dist_eq_norm] at htri
    linarith only [hd, hClose K, htri]

theorem compact_family_bounded_lipschitz_approximation (X : Type*) [MetricSpace X] [CompactSpace X]
    (H : Set C(X, ℂ)) (hH : IsCompact H) (ε : ℝ) (hε : 0 < ε) :
    ∃ B L : ℝ, 0 < B ∧ 0 < L ∧ ∃ P : Finset C(X, ℂ),
      (∀ G ∈ P, (∀ x, ‖G x‖ ≤ B) ∧ LipschitzWith (Real.toNNReal L) G) ∧
      ∀ F ∈ H, ∃ G ∈ P, ‖F-G‖ < ε := by
  obtain ⟨P, hP, hClose⟩ := compact_family_finite_lipschitz_approximation X H hH ε hε
  have ha : ∀ G : C(X, ℂ), ∃ L : ℝ≥0, G ∈ P → LipschitzWith L G := by
    intro G
    by_cases hG : G ∈ P
    · obtain ⟨L, hL⟩ := hP G hG
      exact ⟨L, fun _ => hL⟩
    · exact ⟨0, fun h => (hG h).elim⟩
  choose l hl using ha
  let B : ℝ := 1+∑ G ∈ P, ‖G‖
  let L : ℝ≥0 := 1+∑ G ∈ P, l G
  have hB : 0 < B := by dsimp only [B]; positivity
  have hL : 0 < L := by dsimp only [L]; positivity
  refine ⟨B, (L : ℝ), hB, by exact_mod_cast hL, P, ?_, hClose⟩
  intro G hG
  constructor
  · intro x
    have hsum := Finset.single_le_sum (f := fun F : C(X, ℂ) => ‖F‖) (fun F _ => norm_nonneg F) hG
    exact (G.norm_coe_le_norm x).trans (by dsimp only [B]; linarith only [hsum])
  · have hsum := Finset.single_le_sum (f := l) (fun F _ => (show 0 ≤ l F from zero_le)) hG
    have hle : l G ≤ L := by
      dsimp only [L]
      exact hsum.trans (le_add_of_nonneg_left zero_le_one)
    simpa only [Real.toNNReal_coe] using (hl G hG).weaken hle

end Hindman168
