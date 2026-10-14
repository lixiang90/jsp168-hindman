import Hindman168.RoughHorizontalInterpolation

namespace Hindman168
open Polynomial Filter
open scoped BigOperators

def RoughCoefficientModel (w H q e : ℕ) (Z C : ℝ) (theta : ℝ[X]) (M : ℚ[X]) : Prop :=
  M.natDegree ≤ q - e ∧
  (∀ j r, r.Prime → r ∣ (M.coeff j).den → r ≤ w) ∧
  ∀ z : ℕ, z < H → (∃ b : ℤ, M.eval (z : ℚ) = b) ∧
    |theta.eval (z : ℝ) - ((M.eval (z : ℚ) : ℚ) : ℝ)| ≤ C * Z⁻¹ ^ e

theorem rough_coefficient_model_mono {w H q e : ℕ} {Z C C' : ℝ}
    {theta : ℝ[X]} {M : ℚ[X]} (h : RoughCoefficientModel w H q e Z C theta M)
    (hZ : 0 ≤ Z) (hC : C ≤ C') : RoughCoefficientModel w H q e Z C' theta M := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro z hz
  exact ⟨(h.2.2 z hz).1, (h.2.2 z hz).2.trans (mul_le_mul_of_nonneg_right hC (by positivity))⟩

theorem rough_models_integer_data {ι : Type*} (s : Finset ι)
    {w H q : ℕ} {Z C : ℝ} (e : ι → ℕ) (theta : ι → ℝ[X]) (M : ι → ℚ[X])
    (h : ∀ i ∈ s, RoughCoefficientModel w H q (e i) Z C (theta i) (M i)) :
    ∃ k : ℕ → ι → ℤ, ∀ z, z < H → ∀ i ∈ s,
      |(theta i).eval (z : ℝ) - (k z i : ℝ)| ≤ C * Z⁻¹ ^ e i := by
  classical
  have hx : ∀ z i, ∃ b : ℤ, z < H → i ∈ s →
      |(theta i).eval (z : ℝ) - (b : ℝ)| ≤ C * Z⁻¹ ^ e i := by
    intro z i
    by_cases hz : z < H
    · by_cases hi : i ∈ s
      · obtain ⟨b, hb⟩ := ((h i hi).2.2 z hz).1
        refine ⟨b, fun _ _ => ?_⟩
        simpa only [hb, Rat.cast_intCast] using ((h i hi).2.2 z hz).2
      · exact ⟨0, fun _ hmem => (hi hmem).elim⟩
    · exact ⟨0, fun hlt _ => (hz hlt).elim⟩
  choose k hk using hx
  exact ⟨k, fun z hz i hi => hk z i hz hi⟩

noncomputable def roughDescentConstant (q N : ℕ) (A0 B : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => roughDescentConstant q N A0 B k +
      roughInterpolationConstant q * (2 ^ q * (A0 + (N : ℝ) * B * roughDescentConstant q N A0 B k))

theorem roughDescentConstant_pos (q N : ℕ) {A0 B : ℝ} (hA : 0 < A0) (hB : 0 ≤ B)
    (k : ℕ) : 0 < roughDescentConstant q N A0 B k := by
  induction k with
  | zero => simp [roughDescentConstant]
  | succ k hk =>
    rw [roughDescentConstant]
    have hc := roughInterpolationConstant_pos q
    positivity

theorem roughDescentConstant_le_succ (q N : ℕ) {A0 B : ℝ} (hA : 0 < A0) (hB : 0 ≤ B)
    (k : ℕ) : roughDescentConstant q N A0 B k ≤ roughDescentConstant q N A0 B (k + 1) := by
  rw [roughDescentConstant]
  have hk := roughDescentConstant_pos q N hA hB k
  have hc := roughInterpolationConstant_pos q
  exact le_add_of_nonneg_right (by positivity)

theorem rough_descent_step_constant_bound {ι : Type*} (s v : Finset ι) (hvs : v ⊆ s)
    {q e k : ℕ} (heq : e ≤ q) {A0 B : ℝ} (hA : 0 < A0) (hB : 0 ≤ B) :
    roughInterpolationConstant q *
      (2 ^ e * (A0 + ∑ _i ∈ v, B * roughDescentConstant q s.card A0 B k)) ≤
      roughDescentConstant q s.card A0 B (k + 1) := by
  let C := roughDescentConstant q s.card A0 B k
  have hC : 0 < C := roughDescentConstant_pos q s.card hA hB k
  have hc := roughInterpolationConstant_pos q
  have hsum : (∑ _i ∈ v, B * C) ≤ (s.card : ℝ) * B * C := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hn : (v.card : ℝ) ≤ s.card := by exact_mod_cast Finset.card_le_card hvs
    calc
      (v.card : ℝ) * (B * C) ≤ (s.card : ℝ) * (B * C) := mul_le_mul_of_nonneg_right hn (by positivity)
      _ = _ := by ring
  have hp : (2 : ℝ) ^ e ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) heq
  change roughInterpolationConstant q * (2 ^ e * (A0 + ∑ _i ∈ v, B * C)) ≤ _
  calc
    _ ≤ roughInterpolationConstant q * (2 ^ q * (A0 + (s.card : ℝ) * B * C)) := by gcongr
    _ ≤ C + roughInterpolationConstant q * (2 ^ q * (A0 + (s.card : ℝ) * B * C)) := le_add_of_nonneg_left hC.le
    _ = _ := rfl

end Hindman168
