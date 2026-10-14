import Hindman168.FiniteCandidateDenseRows
import Mathlib.Order.Interval.Finset.Nat

/-! Genuine finite NATURAL label thinning retains enough directions for
integer monomial spanning. All labels are positive bounded multipliers;
the exact card loss is proved, with no fixed-label oracle. -/
namespace Hindman168
open scoped BigOperators Classical

theorem finite_positive_nat_label_subset {α : Type*} (S : Finset α) (V : ℕ) (hV : 0 < V)
    (P : ℕ → α → Prop) (hProduce : ∀ x ∈ S, ∃ m : ℕ, 0 < m ∧ m ≤ V ∧ P m x) :
    ∃ m : ℕ, 0 < m ∧ m ≤ V ∧ ∃ T : Finset α,
      T ⊆ S ∧ S.card ≤ V*T.card ∧ ∀ x ∈ T, P m x := by
  let A := Finset.Icc 1 V
  have hA : A.Nonempty := ⟨1,Finset.mem_Icc.mpr ⟨le_rfl,hV⟩⟩
  have hCovered : S.filter (fun x => ∃ m ∈ A, P m x)=S := by
    ext x
    constructor
    · exact fun h => (Finset.mem_filter.mp h).1
    · intro hx
      obtain ⟨m,hm,hmV,h⟩ := hProduce x hx
      exact Finset.mem_filter.mpr ⟨hx,m,Finset.mem_Icc.mpr ⟨hm,hmV⟩,h⟩
  obtain ⟨m,hmA,hMax⟩ := Finset.exists_max_image A (fun m => (S.filter (P m)).card) hA
  have hSum := finite_candidate_origin_count_le_sum S A P
  rw [hCovered] at hSum
  have hBound : S.card ≤ V*(S.filter (P m)).card := by
    calc
      _ ≤ ∑ k ∈ A, (S.filter (P k)).card := hSum
      _ ≤ ∑ _k ∈ A, (S.filter (P m)).card := Finset.sum_le_sum hMax
      _ = V*(S.filter (P m)).card := by simp [A,Nat.card_Icc]
  exact ⟨m,(Finset.mem_Icc.mp hmA).1,(Finset.mem_Icc.mp hmA).2,S.filter (P m),
    Finset.filter_subset _ _,hBound,fun x hx => (Finset.mem_filter.mp hx).2⟩

theorem finite_dense_direction_label_thinning {α : Type*}
    (S : Finset α) (d V K n : ℕ) (hV : 0 < V)
    (hDense : (d*V)*K^n < S.card*K)
    (P : ℕ → α → Prop) (hProduce : ∀ x ∈ S, ∃ m : ℕ, 0 < m ∧ m ≤ V ∧ P m x) :
    ∃ m : ℕ, 0 < m ∧ m ≤ V ∧ ∃ T : Finset α,
      T ⊆ S ∧ d*K^n < T.card*K ∧ ∀ x ∈ T, P m x := by
  obtain ⟨m,hm,hmV,T,hTS,hCard,hLabels⟩ := finite_positive_nat_label_subset S V hV P hProduce
  have h : V*(d*K^n) < V*(T.card*K) := by
    calc
      _ = (d*V)*K^n := by ring
      _ < S.card*K := hDense
      _ ≤ (V*T.card)*K := Nat.mul_le_mul_right K hCard
      _ = _ := by ring
  exact ⟨m,hm,hmV,T,hTS,Nat.lt_of_mul_lt_mul_left h,hLabels⟩

end Hindman168
