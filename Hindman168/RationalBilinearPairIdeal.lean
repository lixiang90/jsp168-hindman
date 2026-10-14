import Hindman168.FiniteVectorPolynomialMixedSubspaces

/-! An alternating bilinear operation on the rational span of two
vectors and an actual stable subspace. If the pair bracket lies in N,
then every bracket of span_Q{u,w}+N with itself lies in N. -/

namespace Hindman168
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]

theorem rationalBilinearPairSpan_mem
    (N : Submodule ℚ E) (B : E →L[ℝ] (E →L[ℝ] E))
    (hself : ∀ v, B v v = 0) (hskew : ∀ v w, B v w = -B w v)
    (u w : E) (huw : B u w ∈ N)
    {a b : E} (ha : a ∈ Submodule.span ℚ ({u, w} : Set E))
    (hb : b ∈ Submodule.span ℚ ({u, w} : Set E)) : B a b ∈ N := by
  let S := Submodule.span ℚ ({u, w} : Set E)
  have hgen : ∀ x ∈ ({u, w} : Set E), ∀ y ∈ ({u, w} : Set E), B x y ∈ N := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rw [hself]; exact N.zero_mem
    · exact huw
    · rw [hskew]; exact N.neg_mem huw
    · rw [hself]; exact N.zero_mem
  have hsecond : ∀ x ∈ ({u, w} : Set E), ∀ y ∈ S, B x y ∈ N := by
    intro x hx y hy
    let A : E →ₗ[ℚ] E := (B x).toLinearMap.restrictScalars ℚ
    have hs : S ≤ N.comap A := Submodule.span_le.mpr (hgen x hx)
    exact hs hy
  let A : E →ₗ[ℚ] E := (B.flip b).toLinearMap.restrictScalars ℚ
  have hs : S ≤ N.comap A := by
    apply Submodule.span_le.mpr
    intro x hx
    exact hsecond x hx b hb
  exact hs ha

theorem rationalBilinearPairIdeal_mem
    (V N : Submodule ℚ E) (hNV : N ≤ V)
    (B : E →L[ℝ] (E →L[ℝ] E))
    (hself : ∀ v, B v v = 0) (hskew : ∀ v w, B v w = -B w v)
    (hideal : ∀ v ∈ V, ∀ n ∈ N, B v n ∈ N)
    {u w : E} (hu : u ∈ V) (hw : w ∈ V) (huw : B u w ∈ N)
    {a b : E} (ha : a ∈ Submodule.span ℚ ({u, w} : Set E) ⊔ N)
    (hb : b ∈ Submodule.span ℚ ({u, w} : Set E) ⊔ N) : B a b ∈ N := by
  let S := Submodule.span ℚ ({u, w} : Set E)
  let P := S ⊔ N
  have hsV : S ≤ V := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hw
  have hpV : P ≤ V := sup_le hsV hNV
  have hfirst : ∀ x ∈ ({u, w} : Set E), B x b ∈ N := by
    intro x hx
    have hxS : x ∈ S := Submodule.subset_span hx
    let A : E →ₗ[ℚ] E := (B x).toLinearMap.restrictScalars ℚ
    have hs : S ≤ N.comap A := fun _ hy =>
      rationalBilinearPairSpan_mem N B hself hskew u w huw hxS hy
    have hn : N ≤ N.comap A := fun _ hy => hideal x (hsV hxS) _ hy
    exact (sup_le hs hn) hb
  let A : E →ₗ[ℚ] E := (B.flip b).toLinearMap.restrictScalars ℚ
  have hs : S ≤ N.comap A := Submodule.span_le.mpr hfirst
  have hn : N ≤ N.comap A := by
    intro n hn
    change B n b ∈ N
    rw [hskew]
    exact N.neg_mem (hideal b (hpV hb) n hn)
  exact (sup_le hs hn) ha

end Hindman168
