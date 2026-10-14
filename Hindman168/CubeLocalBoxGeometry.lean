import Hindman168.AlignmentCeilBoxes
import Mathlib.Tactic

/-! Explicit real endpoint cube geometry, including ceil rounding and all vertices. -/
namespace Hindman168
open scoped BigOperators Classical

theorem cube_scaled_vertex_bound {d : ℕ} (x : Fin (d+1) → ℝ)
    (beta L δ : ℝ) (hL : 0 < L) (hδ : 0 ≤ δ)
    (hbase : |x 0-beta*L| ≤ δ*L) (hinc : ∀ i : Fin d, |x i.succ| ≤ δ*L)
    (V : Finset (Fin d)) :
    |(x 0 + ∑ i ∈ V, x i.succ)/L-beta| ≤ ((d : ℝ)+1)*δ := by
  have hcard : (V.card : ℝ) ≤ d := by
    have hc : V.card ≤ d := by simpa only [Fintype.card_fin] using V.card_le_univ
    exact_mod_cast hc
  have hs : |∑ i ∈ V, x i.succ| ≤ (d : ℝ)*(δ*L) := by
    calc
      _ ≤ ∑ i ∈ V, |x i.succ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ V, δ*L := Finset.sum_le_sum (fun i _ => hinc i)
      _ = (V.card : ℝ)*(δ*L) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (mul_nonneg hδ hL.le)
  have hid : (x 0 + ∑ i ∈ V, x i.succ)/L-beta = ((x 0-beta*L)+∑ i ∈ V, x i.succ)/L := by
    field_simp
    ring
  rw [hid,abs_div,abs_of_pos hL]
  apply (div_le_iff₀ hL).mpr
  have ht := (abs_add_le (x 0-beta*L) (∑ i ∈ V, x i.succ)).trans (add_le_add hbase hs)
  nlinarith only [ht]

theorem cube_local_ceil_endpoint_bound {d : ℕ} (lo hi : Fin (d+1) → ℝ)
    (beta L δ : ℝ) (hL : 1 ≤ L)
    (hbase : |lo 0-beta*L| ≤ δ*L ∧ |hi 0-beta*L| ≤ δ*L)
    (hinc : ∀ i : Fin d, |lo i.succ| ≤ δ*L ∧ |hi i.succ| ≤ δ*L) :
    ∀ j, |(⌈lo j⌉ : ℝ)| ≤ (|beta|+δ+1)*L ∧ |(⌈hi j⌉ : ℝ)| ≤ (|beta|+δ+1)*L := by
  have hL0 : 0 ≤ L := by linarith
  have hB : ∀ j, |lo j| ≤ (|beta|+δ)*L ∧ |hi j| ≤ (|beta|+δ)*L := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · have hb : |beta*L| = |beta| * L := by rw [abs_mul,abs_of_nonneg hL0]
      have hl := abs_add_le (lo 0-beta*L) (beta*L)
      have hu := abs_add_le (hi 0-beta*L) (beta*L)
      rw [sub_add_cancel,hb] at hl hu
      constructor <;> nlinarith [hbase.1,hbase.2]
    · have hpos : 0 ≤ |beta| * L := mul_nonneg (abs_nonneg _) hL0
      constructor <;> nlinarith [(hinc i).1,(hinc i).2]
  intro j
  exact ⟨alignment_ceil_endpoint_bound _ L (|beta|+δ) hL (hB j).1,
    alignment_ceil_endpoint_bound _ L (|beta|+δ) hL (hB j).2⟩

theorem cube_local_ceil_vertex_bound {d : ℕ} (lo hi : Fin (d+1) → ℝ)
    (v x : Fin (d+1) → ℤ) (t : ℤ) (beta L δ : ℝ) (hL : 0 < L) (hδ : 0 ≤ δ)
    (hbase : |lo 0-beta*L| ≤ δ*L ∧ |hi 0-beta*L| ≤ δ*L)
    (hinc : ∀ i : Fin d, |lo i.succ| ≤ δ*L ∧ |hi i.succ| ≤ δ*L)
    (hx : x ∈ alignmentBoxClass (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) v t)
    (V : Finset (Fin d)) :
    |((x 0 + ∑ i ∈ V, x i.succ : ℤ) : ℝ)/L-beta| ≤ ((d : ℝ)+1)*δ := by
  have hm := (alignment_ceil_box_mem lo hi t v x).mp hx
  have hb : |(x 0 : ℝ)-beta*L| ≤ δ*L := by
    rw [abs_le]
    constructor <;> linarith [(abs_le.mp hbase.1).1,(abs_le.mp hbase.2).2,(hm 0).1.1,(hm 0).1.2]
  have hi' : ∀ i : Fin d, |(x i.succ : ℝ)| ≤ δ*L := by
    intro i
    rw [abs_le]
    constructor <;> linarith [(abs_le.mp (hinc i).1).1,(abs_le.mp (hinc i).2).2,(hm i.succ).1.1,(hm i.succ).1.2]
  simpa only [Int.cast_add,Int.cast_sum] using cube_scaled_vertex_bound (fun j => (x j : ℝ)) beta L δ hL hδ hb hi' V

theorem cube_local_ceil_side_bounds (lo hi L a b : ℝ) (hL : 1 ≤ L)
    (ha : 2 ≤ a*L) (hlen : a*L ≤ hi-lo ∧ hi-lo ≤ b*L) :
    (a/2)*L ≤ (⌈hi⌉ : ℝ)-(⌈lo⌉ : ℝ) ∧ (⌈hi⌉ : ℝ)-(⌈lo⌉ : ℝ) ≤ (b+1)*L := by
  have hl0 := Int.le_ceil lo
  have hl1 := Int.ceil_lt_add_one lo
  have hu0 := Int.le_ceil hi
  have hu1 := Int.ceil_lt_add_one hi
  constructor <;> nlinarith [hlen.1,hlen.2]

end Hindman168
