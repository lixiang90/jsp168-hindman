import Hindman168.RoughDescentModels

namespace Hindman168
open Polynomial Filter
open scoped Topology BigOperators

def RoughHorizontalSystem {ι : Type*} (s : Finset ι) (e : ι → ℕ)
    (w H q t m : ℕ) (S Z A0 B : ℝ) (theta : ι → ℝ[X])
    (p : ι → ℕ → ℕ) (c : ι → ℕ → ι → ℤ) : Prop :=
  0 < m ∧ (∀ r, r.Prime → r ∣ m → r ≤ w) ∧
  (∀ z : ℕ, z < H → S ≤ (t + m * z : ℕ) ∧ (t + m * z : ℕ) < 2 * S) ∧
  (∀ z : ℕ, z < H → (primorial w).Coprime (t + m * z)) ∧
  ∀ i ∈ s,
    ((C (t : ℝ) + C (m : ℝ) * X) ^ e i * theta i).natDegree ≤ q ∧
    (∀ z, z < H → p i z = 1 ∨ p i z = t + m * z) ∧
    (∀ z, z < H → ∀ j ∈ s.filter (fun j => e i < e j),
      |(c i z j : ℝ)| ≤ B * (p i z : ℝ) ^ (e j - e i)) ∧
    (∀ z, z < H →
      ‖(((p i z : ℝ) ^ e i * ((theta i).eval (z : ℝ) +
        ∑ j ∈ s.filter (fun j => e i < e j), (c i z j : ℝ) * (theta j).eval (z : ℝ)) : ℝ) : UnitAddCircle)‖ ≤
        A0 * ((p i z : ℝ) / Z) ^ e i)

theorem rough_descent_system_step
    {α ι : Type*} {l : Filter α} {W : α → ℕ} (hW : Tendsto W l atTop)
    {S Z : α → ℝ} (hg : PowerDominates l Z S)
    (hS : ∀ᶠ w in l, 1 ≤ S w) (hZ : ∀ᶠ w in l, 0 < Z w)
    (s : Finset ι) (e : ι → ℕ) (q H k : ℕ) (hH : 2 * q + 2 ≤ H)
    (A0 B : ℝ) (hA : 0 < A0) (hB : 0 ≤ B) (i : ι) (hi : i ∈ s)
    (hei : 0 < e i) (heq : e i ≤ q) :
    ∀ᶠ w in l, ∀ (t m : ℕ) (theta : ι → ℝ[X])
      (p : ι → ℕ → ℕ) (c : ι → ℕ → ι → ℤ) (M : ι → ℚ[X]),
      RoughHorizontalSystem s e (W w) H q t m (S w) (Z w) A0 B theta p c →
      (∀ j ∈ s, e i < e j → RoughCoefficientModel (W w) H q (e j) (Z w)
        (roughDescentConstant q s.card A0 B k) (theta j) (M j)) →
      ∃ Mi : ℚ[X], RoughCoefficientModel (W w) H q (e i) (Z w)
        (roughDescentConstant q s.card A0 B (k + 1)) (theta i) Mi := by
  let v := s.filter (fun j => e i < e j)
  let K := roughDescentConstant q s.card A0 B k
  have hK : 0 < K := roughDescentConstant_pos q s.card hA hB k
  have hh := rough_horizontal_interpolation_step hW hg hS hZ (e i) q H hei heq hH
    v (fun _ => K) (fun _ => B) (fun j => e j - e i) A0 hA
    (fun _ _ => hK.le) (fun _ _ => hB)
  filter_upwards [hh, hZ] with w hw hz
  intro t m theta p c M hsys hmodels
  obtain ⟨hm, hmsmooth, hprog, hrough, hdata⟩ := hsys
  have hiData := hdata i hi
  have hvmodels : ∀ j ∈ v, RoughCoefficientModel (W w) H q (e j) (Z w) K (theta j) (M j) := by
    intro j hj
    exact hmodels j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
  obtain ⟨ints, hints⟩ := rough_models_integer_data v e theta M hvmodels
  have herr : ∀ z, z < H → ∀ j ∈ v,
      |(theta j).eval (z : ℝ) - (ints z j : ℝ)| ≤ K * (Z w)⁻¹ ^ (e i + (e j - e i)) := by
    intro z hzH j hj
    rw [Nat.add_sub_cancel' (Finset.mem_filter.mp hj).2.le]
    exact hints z hzH j hj
  obtain ⟨Mi, hMi⟩ := hw t m (theta i) (p i) (c i) ints
    (fun z j => (theta j).eval (z : ℝ)) hm hmsmooth hprog hrough hiData.1
    hiData.2.1 hiData.2.2.1 herr hiData.2.2.2
  refine ⟨Mi, rough_coefficient_model_mono hMi hz.le ?_⟩
  exact rough_descent_step_constant_bound s v (Finset.filter_subset _ _) heq hA hB

end Hindman168
