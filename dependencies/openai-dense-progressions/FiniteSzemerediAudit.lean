import OAI.Compatibility.FiniteIntegerAP

/-! Author-side dependency audit. This bridge states density and actual
integer progressions directly, independently of the dependency's HasAP name.
It does not assert the Hindman sums/products target. -/
namespace JSP168DependencyAudit

theorem actual_finite_dense_progression (H : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℕ, 0 < K ∧ ∀ U : Finset ℕ,
      U ⊆ Finset.range K → δ*(K : ℝ) ≤ U.card →
      ∃ a b : ℕ, 0 < b ∧ b < K ∧ ∀ z : ℕ, z < H → a+b*z ∈ U := by
  obtain ⟨K,hK,hAP⟩ := OAI.Erdos3.fixed_density_hasAP (max 2 H) hδ
  refine ⟨K,hK,?_⟩
  intro U hU hd
  obtain ⟨a,b,hb,hterms⟩ := hAP K (le_refl K) U hU hd
  have h1 : 1 < max 2 H := lt_of_lt_of_le (by omega) (le_max_left _ _)
  have hterm1 := Finset.mem_range.mp (hU (hterms 1 h1))
  have hbK : b < K := by omega
  exact ⟨a,b,hb,hbK,fun z hz => by
    simpa only [Finset.mem_coe, mul_comm] using hterms z (hz.trans_le (le_max_right 2 H))⟩

end JSP168DependencyAudit

#print OAI.Erdos3.HasAP
#print OAI.Erdos3.FixedDensity.HasUniformDenseAPCount
#print OAI.Erdos3.FixedDensity.cyclicAPCount
#print OAI.Erdos3.fixed_density_hasAP
#print axioms OAI.Erdos3.FixedDensity.szemeredi
#print axioms OAI.Erdos3.FixedDensity.cyclicAPVal_isIntegerAP
#print axioms OAI.Erdos3.fixed_density_hasAP
#print axioms JSP168DependencyAudit.actual_finite_dense_progression
