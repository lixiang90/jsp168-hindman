import Hindman168.LinearNearestIntegerHitCount
import Hindman168.UnitCirclePhaseDistance

namespace Hindman168
open scoped BigOperators Classical

theorem unit_circle_integer_translate (y : ℝ) (m : ℤ) :
    ((y-(m : ℝ) : ℝ) : UnitAddCircle) = (y : UnitAddCircle) := by
  have hz : ((m : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨m, by simp⟩
  rw [AddCircle.coe_sub, hz, sub_zero]

theorem unit_circle_residue_row_value (x b : ℝ) (q n : ℕ) :
    ((b+(n%q : ℕ)*x+(n/q : ℕ)*((q : ℝ)*x-(round ((q : ℝ)*x) : ℝ)) : ℝ) : UnitAddCircle) =
      ((b+(n : ℝ)*x : ℝ) : UnitAddCircle) := by
  have hn : (n : ℝ) = (n%q : ℕ)+ (q : ℝ)*(n/q : ℕ) := by
    exact_mod_cast (Nat.mod_add_div n q).symm
  have he : b+(n%q : ℕ)*x+(n/q : ℕ)*((q : ℝ)*x-(round ((q : ℝ)*x) : ℝ)) =
      b+(n : ℝ)*x-(((n/q : ℕ) : ℤ)*round ((q : ℝ)*x) : ℤ) := by
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [hn]
    ring
  rw [he, unit_circle_integer_translate]

/-- An actual modular interval-hit bound, after partitioning the original
indices into residue rows. It includes resonant and negative increments. -/
theorem unit_circle_progression_hit_count (s : Finset ℕ) (N q : ℕ) (hq : 0 < q)
    (hsN : s ⊆ Finset.range N) (x b ε : ℝ) (hε : 0 ≤ ε) (hε2 : 2*ε ≤ 1)
    (hu : |(q : ℝ)*x-(round ((q : ℝ)*x) : ℝ)| ≤ 1)
    (hhit : ∀ n ∈ s, ‖((b+(n : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ ε) :
    |(q : ℝ)*x-(round ((q : ℝ)*x) : ℝ)| * (s.card : ℝ) ≤
      (|(q : ℝ)*x-(round ((q : ℝ)*x) : ℝ)| * (N : ℝ)+3*(q : ℝ))*
        (|(q : ℝ)*x-(round ((q : ℝ)*x) : ℝ)|+2*ε) := by
  let u := (q : ℝ)*x-(round ((q : ℝ)*x) : ℝ)
  let J := N/q+1
  let row := fun r : ℕ => s.filter (fun n => n%q=r)
  let indices := fun r : ℕ => (row r).image (fun n => n/q)
  have hrow : ∀ r, ((row r).card : ℝ)*|u| ≤
      (|u| *(J : ℝ)+2*ε+1)*(|u|+2*ε) := by
    intro r
    have hinj : Set.InjOn (fun n : ℕ => n/q) (row r) := by
      intro n hn m hm he
      change n/q = m/q at he
      have hnmod := (Finset.mem_filter.mp hn).2
      have hmmod := (Finset.mem_filter.mp hm).2
      have hn' := Nat.mod_add_div n q
      have hm' := Nat.mod_add_div m q
      rw [hnmod, he] at hn'
      rw [hmmod] at hm'
      omega
    have hc : (indices r).card = (row r).card := Finset.card_image_of_injOn hinj
    have hsub : indices r ⊆ Finset.range J := by
      intro j hj
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hj
      have hnN := Finset.mem_range.mp (hsN (Finset.mem_filter.mp hn).1)
      exact Finset.mem_range.mpr (by
        have hdiv := Nat.div_le_div_right hnN.le (c := q)
        dsimp only [J]
        omega)
    have hsmall : ∀ j ∈ indices r,
        |b+(r : ℝ)*x+(j : ℝ)*u-(round (b+(r : ℝ)*x+(j : ℝ)*u) : ℝ)| ≤ ε := by
      intro j hj
      obtain ⟨n, hn, hnj⟩ := Finset.mem_image.mp hj
      have hnmod := (Finset.mem_filter.mp hn).2
      have hv := unit_circle_residue_row_value x b q n
      rw [hnmod, hnj] at hv
      have hs := hhit n (Finset.mem_filter.mp hn).1
      rw [← hv, UnitAddCircle.norm_eq] at hs
      exact hs
    have hb := linear_nearest_integer_hit_count (indices r) J hsub
      (b+(r : ℝ)*x) u ε hε hsmall
    rw [hc] at hb
    simpa only [mul_comm] using hb
  have hcard := Finset.card_eq_sum_card_fiberwise (f := fun n : ℕ => n%q)
    (s := s) (t := Finset.range q) (fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hq))
  have hcr := congrArg (fun n : ℕ => (n : ℝ)) hcard
  push_cast at hcr
  have hsum : |u| *(s.card : ℝ) ≤
      (q : ℝ)*(|u| *(J : ℝ)+2*ε+1)*(|u|+2*ε) := by
    rw [hcr, Finset.mul_sum]
    calc
      _ ≤ ∑ r ∈ Finset.range q, ((|u| *(J : ℝ)+2*ε+1)*(|u|+2*ε)) := by
        apply Finset.sum_le_sum
        intro r _
        simpa only [row, mul_comm] using hrow r
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hJ : (q : ℝ)*(J : ℝ) ≤ (N : ℝ)+(q : ℝ) := by
    have hd := Nat.div_mul_le_self N q
    have hdr : (N/q : ℕ)*(q : ℝ) ≤ N := by exact_mod_cast hd
    dsimp only [J]
    push_cast
    nlinarith
  have hfactor : (q : ℝ)*(|u| *(J : ℝ)+2*ε+1) ≤ |u| *(N : ℝ)+3*(q : ℝ) := by
    have hmult := mul_le_mul_of_nonneg_left hJ (abs_nonneg u)
    have hqeps := mul_le_mul_of_nonneg_left hε2 (Nat.cast_nonneg (α := ℝ) q)
    have hqu := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg (α := ℝ) q)
    change |u| ≤ 1 at hu
    nlinarith
  exact hsum.trans (mul_le_mul_of_nonneg_right hfactor (by positivity))

end Hindman168

