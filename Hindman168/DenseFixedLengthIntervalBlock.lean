import Hindman168.FiniteDenseWitnessSelection
import Mathlib.Order.Interval.Finset.Nat

/-! Actual FIXED-LENGTH complete block selection from dense original range hits.
The final remainder is bounded and discarded explicitly, never assumed dense. -/
namespace Hindman168
open scoped Classical

theorem dense_fixed_length_interval_block (N K : ℕ) (hK : 0 < K) (hq : 0 < N/K)
    (δ : ℝ) (hδ : 0 < δ) (htail : 2*(K : ℝ) ≤ δ*(N : ℝ))
    (U : Finset ℕ) (hU : U ⊆ Finset.range N) (hdense : δ*(N : ℝ) ≤ U.card) :
    ∃ j : ℕ, j < N/K ∧ (j+1)*K ≤ N ∧
      (δ/2)*(K : ℝ) ≤ ((Finset.range K).filter (fun n => j*K+n ∈ U)).card := by
  let J := N/K
  let L := K
  have hJ : 0 < J := hq
  have hL : 0 < L := hK
  have hJL : J*L ≤ N := by dsimp only [J,L]; exact Nat.div_mul_le_self N K
  let T := U.filter (fun n => n < J*L)
  let R := U.filter (fun n => ¬ n < J*L)
  have hR : R ⊆ Finset.Ico (J*L) N := by
    intro n hn
    obtain ⟨hnU,hnTail⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Ico.mpr ⟨Nat.le_of_not_gt hnTail,Finset.mem_range.mp (hU hnU)⟩
  have hRcard : R.card ≤ K := by
    have hr := (Finset.card_le_card hR).trans (show (Finset.Ico (J*L) N).card ≤ K from by
      rw [Nat.card_Ico]
      dsimp only [J,L]
      rw [← Nat.mod_eq_sub_div_mul]
      exact (Nat.mod_lt N hK).le)
    exact hr
  have hpart : T.card+R.card=U.card := Finset.card_filter_add_card_filter_not (s := U) (fun n => n < J*L)
  have hdT : (δ/2)*(N : ℝ) ≤ T.card := by
    have he : (T.card : ℝ)+(R.card : ℝ)=U.card := by exact_mod_cast hpart
    have hr : (R.card : ℝ) ≤ K := by exact_mod_cast hRcard
    linarith
  have hN : 0 < N := by
    apply Nat.pos_of_ne_zero
    intro hz
    simp only [hz,Nat.zero_div,lt_self_iff_false] at hq
  have hT : T.Nonempty := Finset.card_pos.mp (by
    have hp : (0 : ℝ) < T.card := lt_of_lt_of_le (by positivity : 0 < (δ/2)*(N : ℝ)) hdT
    exact_mod_cast hp)
  have hw : ∀ n ∈ T, ∃ j ∈ Finset.range J, n/L=j := by
    intro n hn
    have hlt := (Finset.mem_filter.mp hn).2
    have hj : n/L < J := by
      by_contra! h
      have hm := Nat.mul_le_mul_right L h
      have hd := Nat.div_mul_le_self n L
      omega
    exact ⟨n/L,Finset.mem_range.mpr hj,rfl⟩
  obtain ⟨j,hj,V,hVT,_,hcard,hlabel⟩ := finite_dense_witness_selection T hT (Finset.range J)
    (fun n j => n/L=j) hw
  have hsub : V.image (fun n => n%L) ⊆ (Finset.range L).filter (fun n => j*L+n ∈ U) := by
    intro n hn
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
    have hdiv := hlabel a ha
    have he : j*L+a%L=a := by
      have hh := Nat.mod_add_div a L
      rw [hdiv] at hh
      simpa only [Nat.mul_comm,Nat.add_comm] using hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt a hL),
      by rw [he]; exact (Finset.mem_filter.mp (hVT ha)).1⟩
  have hinj : Set.InjOn (fun n : ℕ => n%L) V := by
    intro a ha b hb he
    change a%L=b%L at he
    have ha' := Nat.mod_add_div a L
    have hb' := Nat.mod_add_div b L
    rw [hlabel a ha] at ha'
    rw [hlabel b hb] at hb'
    omega
  have hVcard : V.card ≤ ((Finset.range L).filter (fun n => j*L+n ∈ U)).card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  have hblock : (δ/2)*(L : ℝ) ≤ V.card := by
    have hc : (T.card : ℝ) ≤ (J : ℝ)*(V.card : ℝ) := by simpa only [Finset.card_range] using hcard
    have hnr : (J : ℝ)*(L : ℝ) ≤ N := by exact_mod_cast hJL
    have hm := mul_le_mul_of_nonneg_left hnr (by positivity : 0 ≤ δ/2)
    have hjp : (0 : ℝ) < J := by exact_mod_cast hJ
    nlinarith
  have hj' : j < J := Finset.mem_range.mp hj
  have hend : (j+1)*L ≤ N := (Nat.mul_le_mul_right L (Nat.succ_le_iff.mpr hj')).trans hJL
  exact ⟨j,hj',hend,hblock.trans (by exact_mod_cast hVcard)⟩

end Hindman168
