import OAI.Compatibility.FiniteIntegerAP
import Hindman168.DenseFixedLengthIntervalBlock

/-! Arbitrary-length dense integer APs from the attributed, checked OpenAI
finite Szemeredi closure. These results keep actual Finset membership and
positive bounded steps; they do not assert simultaneous sums and products. -/
namespace Hindman168
open scoped Classical

theorem finite_dense_arithmetic_progression (H : ℕ) {δ : ℝ} (hδ : 0 < δ) :
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
    simpa only [Finset.mem_coe,mul_comm] using hterms z (hz.trans_le (le_max_right 2 H))⟩

theorem dense_range_bounded_progression (H : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℕ, 0 < K ∧ ∀ N : ℕ, K ≤ N → 2*(K : ℝ) ≤ δ*(N : ℝ) →
      ∀ U : Finset ℕ, U ⊆ Finset.range N → δ*(N : ℝ) ≤ U.card →
      ∃ a b : ℕ, 0 < b ∧ b < K ∧ ∀ z : ℕ, z < H → a+b*z ∈ U := by
  obtain ⟨K,hK,hAP⟩ := finite_dense_arithmetic_progression (δ := δ/2) H
    (div_pos hδ (by norm_num : (0 : ℝ) < 2))
  refine ⟨K,hK,?_⟩
  intro N hNK htail U hU hd
  obtain ⟨j,_hj,_hend,hblock⟩ := dense_fixed_length_interval_block N K hK
    (Nat.div_pos hNK hK) δ hδ htail U hU hd
  let V := (Finset.range K).filter (fun n => j*K+n ∈ U)
  obtain ⟨a,b,hb,hbK,hterms⟩ := hAP V (fun _ hx => (Finset.mem_filter.mp hx).1) hblock
  refine ⟨j*K+a,b,hb,hbK,?_⟩
  intro z hz
  have hh := (Finset.mem_filter.mp (hterms z hz)).2
  simpa only [Nat.add_assoc] using hh

end Hindman168
