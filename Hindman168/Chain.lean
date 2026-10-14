import Hindman168.FiniteSums
import Hindman168.Ramsey
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Ordered tails and singleton pivots

The chain has `T₁ < ... < Tₘ < i₁ < ... < iₘ`, with every tail nonempty.
Blocks are `T_d ∪ {i_d}`. In particular the whole blocks are disjoint but
need not be ordered: all the tails occur before all the pivots.
-/

namespace Hindman168

open scoped BigOperators

def Before (A B : Finset ℕ) : Prop := ∀ a ∈ A, ∀ b ∈ B, a < b

structure Chain (m : ℕ) where
  tail : Fin m → Finset ℕ
  pivot : Fin m → ℕ
  tail_nonempty : ∀ i, (tail i).Nonempty
  tail_before : ∀ i j, i < j → Before (tail i) (tail j)
  tails_before_pivots : ∀ i j, ∀ a ∈ tail i, a < pivot j
  pivot_strictMono : StrictMono pivot

namespace Chain

def block {m : ℕ} (C : Chain m) (i : Fin m) : Finset ℕ := insert (C.pivot i) (C.tail i)

theorem pivot_not_mem {m : ℕ} (C : Chain m) (i : Fin m) : C.pivot i ∉ C.tail i := by
  intro hi
  exact (lt_irrefl _ (C.tails_before_pivots i i _ hi))

theorem block_nonempty {m : ℕ} (C : Chain m) (i : Fin m) : (C.block i).Nonempty :=
  Finset.insert_nonempty _ _

theorem blocks_disjoint {m : ℕ} (C : Chain m) {i j : Fin m} (hij : i ≠ j) :
    Disjoint (C.block i) (C.block j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  simp only [block, Finset.mem_insert] at hxi hxj
  rcases hxi with hxi | hxi <;> rcases hxj with hxj | hxj
  · exact hij (C.pivot_strictMono.injective (hxi.symm.trans hxj))
  · have hlt := C.tails_before_pivots j i x hxj
    exact (ne_of_lt hlt) hxi
  · have hlt := C.tails_before_pivots i j x hxi
    exact (ne_of_lt hlt) hxj
  · rcases lt_or_gt_of_ne hij with h | h
    · exact lt_irrefl x (C.tail_before i j h x hxi x hxj)
    · exact lt_irrefl x (C.tail_before j i h x hxj x hxi)

theorem union_card {m : ℕ} (C : Chain m) (I : Finset (Fin m)) :
    (I.biUnion C.block).card = ∑ i ∈ I, (C.block i).card :=
  Finset.card_biUnion (fun _ _ _ _ h => C.blocks_disjoint h)

theorem product_union {m : ℕ} (C : Chain m) (I : Finset (Fin m)) (x : ℕ → ℕ) :
    (∏ j ∈ I.biUnion C.block, x j) = ∏ i ∈ I, ∏ j ∈ C.block i, x j :=
  Finset.prod_biUnion (fun _ _ _ _ h => C.blocks_disjoint h)

/-- The exact ordering used by the paper's adding-block family `E_B`. -/
def AddsTo (P : Finset ℕ) (j : ℕ) (T : Finset ℕ) (i : ℕ) : Prop :=
  P.Nonempty ∧ Before P T ∧ (∀ t ∈ T, t < j) ∧ j < i

theorem earlier_adds {m : ℕ} (C : Chain m) (i j : Fin m) (hij : i < j) :
    AddsTo (C.tail i) (C.pivot i) (C.tail j) (C.pivot j) :=
  ⟨C.tail_nonempty i, C.tail_before i j hij,
    C.tails_before_pivots j i, C.pivot_strictMono hij⟩

/-- Allocate prescribed block sizes in positions `0,...,K-1`. The tails use
successive intervals; the singleton pivots use the following `m` positions. -/
theorem allocate_positions {m K : ℕ} (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hbound : (∑ i, q i) ≤ K) :
    ∃ C : Chain m, (∀ i, (C.block i).card = q i) ∧
      (∀ i, C.block i ⊆ Finset.range K) := by
  classical
  let v : Fin m → ℕ := fun i => q i - 1
  let p : ℕ := ∑ i, v i
  let pre : Fin m → ℕ := fun i => ∑ j ∈ Finset.univ.filter (fun j => j < i), v j
  have hv (i : Fin m) : 0 < v i := by
    dsimp [v]
    have := hq i
    omega
  have hp : p + m = ∑ i, q i := by
    calc
      p + m = (∑ i, v i) + (∑ i : Fin m, (1 : ℕ)) := by simp [p]
      _ = ∑ i, (v i + 1) := Finset.sum_add_distrib.symm
      _ = ∑ i, q i := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [v]
        have := hq i
        omega
  have hpre (i j : Fin m) (hij : i < j) : pre i + v i ≤ pre j := by
    have hn : i ∉ Finset.univ.filter (fun j : Fin m => j < i) := by simp
    have hs : insert i (Finset.univ.filter (fun j : Fin m => j < i)) ⊆
        Finset.univ.filter (fun k => k < j) := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · simp [hij]
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hk).2.trans hij⟩
    have ht := Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun k _ _ => Nat.zero_le (v k))
    rw [Finset.sum_insert hn] at ht
    simpa [pre, Nat.add_comm] using ht
  have hprep (i : Fin m) : pre i + v i ≤ p := by
    have hn : i ∉ Finset.univ.filter (fun j : Fin m => j < i) := by simp
    have hs : insert i (Finset.univ.filter (fun j : Fin m => j < i)) ⊆ Finset.univ :=
      Finset.subset_univ _
    have ht := Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun k _ _ => Nat.zero_le (v k))
    rw [Finset.sum_insert hn] at ht
    simpa [pre, p, Nat.add_comm] using ht
  let tails : Fin m → Finset ℕ := fun i => Finset.Ico (pre i) (pre i + v i)
  let pivots : Fin m → ℕ := fun i => p + i.val
  have htail (i : Fin m) : (tails i).Nonempty := by
    refine ⟨pre i, Finset.mem_Ico.mpr ⟨le_rfl, ?_⟩⟩
    have := hv i
    omega
  have htp (i j : Fin m) (a : ℕ) (ha : a ∈ tails i) : a < pivots j := by
    have ha' := (Finset.mem_Ico.mp ha).2
    have := hprep i
    dsimp [pivots]
    omega
  have htt (i j : Fin m) (hij : i < j) : Before (tails i) (tails j) := by
    intro a ha b hb
    have ha' := (Finset.mem_Ico.mp ha).2
    have hb' := (Finset.mem_Ico.mp hb).1
    have := hpre i j hij
    omega
  have hpm : StrictMono pivots := by
    intro i j hij
    exact Nat.add_lt_add_left hij p
  let C : Chain m := ⟨tails, pivots, htail, htt, htp, hpm⟩
  refine ⟨C, ?_, ?_⟩
  · intro i
    rw [block, Finset.card_insert_of_notMem (C.pivot_not_mem i)]
    have hcard : (C.tail i).card = v i := by
      simp [C, tails]
    rw [hcard]
    dsimp [v]
    have := hq i
    omega
  · intro i a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · apply Finset.mem_range.mpr
      have hi := i.is_lt
      have hpk : p + m ≤ K := by omega
      change p + i.val < K
      omega
    · apply Finset.mem_range.mpr
      have ha' := (Finset.mem_Ico.mp ha).2
      have := hprep i
      have hpk : p ≤ K := by omega
      omega

/-- The positional allocation transfers through the increasing enumeration
of any sufficiently large finite index set. -/
theorem allocate_in_finset {m K : ℕ} (A : Finset ℕ) (hcard : A.card = K)
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hbound : (∑ i, q i) ≤ K) :
    ∃ C : Chain m, (∀ i, (C.block i).card = q i) ∧ (∀ i, C.block i ⊆ A) := by
  classical
  obtain ⟨C, hCcard, hCrange⟩ := allocate_positions q hq hbound
  let e : Fin K ↪o ℕ := A.orderEmbOfFin hcard
  let f : ℕ → ℕ := fun a => if ha : a < K then e ⟨a, ha⟩ else 0
  have hf_mem (a : ℕ) (ha : a < K) : f a ∈ A := by
    simp only [f, dif_pos ha]
    exact A.orderEmbOfFin_mem hcard ⟨a, ha⟩
  have hf_lt (a b : ℕ) (ha : a < K) (hb : b < K) (hab : a < b) : f a < f b := by
    simp only [f, dif_pos ha, dif_pos hb]
    exact e.strictMono hab
  have hf_inj (a b : ℕ) (ha : a < K) (hb : b < K) (hab : f a = f b) : a = b := by
    have heq : (⟨a, ha⟩ : Fin K) = ⟨b, hb⟩ := e.injective (by
      simpa only [f, dif_pos ha, dif_pos hb] using hab)
    exact congrArg Fin.val heq
  have ht_bound (i : Fin m) (a : ℕ) (ha : a ∈ C.tail i) : a < K :=
    Finset.mem_range.mp (hCrange i (Finset.mem_insert_of_mem ha))
  have hp_bound (i : Fin m) : C.pivot i < K :=
    Finset.mem_range.mp (hCrange i (Finset.mem_insert_self _ _))
  let tails : Fin m → Finset ℕ := fun i => (C.tail i).image f
  let pivots : Fin m → ℕ := fun i => f (C.pivot i)
  have htn (i : Fin m) : (tails i).Nonempty := (C.tail_nonempty i).image f
  have htt (i j : Fin m) (hij : i < j) : Before (tails i) (tails j) := by
    rintro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    exact hf_lt a' b' (ht_bound i a' ha') (ht_bound j b' hb')
      (C.tail_before i j hij a' ha' b' hb')
  have htp (i j : Fin m) (a : ℕ) (ha : a ∈ tails i) : a < pivots j := by
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    exact hf_lt a' (C.pivot j) (ht_bound i a' ha') (hp_bound j)
      (C.tails_before_pivots i j a' ha')
  have hpm : StrictMono pivots := by
    intro i j hij
    exact hf_lt (C.pivot i) (C.pivot j) (hp_bound i) (hp_bound j)
      (C.pivot_strictMono hij)
  let D : Chain m := ⟨tails, pivots, htn, htt, htp, hpm⟩
  refine ⟨D, ?_, ?_⟩
  · intro i
    have htailcard : (D.tail i).card = (C.tail i).card :=
      Finset.card_image_of_injOn (fun a ha b hb hab =>
        hf_inj a b (ht_bound i a ha) (ht_bound i b hb) hab)
    rw [block, Finset.card_insert_of_notMem (D.pivot_not_mem i), htailcard]
    have hc := hCcard i
    rw [block, Finset.card_insert_of_notMem (C.pivot_not_mem i)] at hc
    exact hc
  · intro i a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hf_mem (C.pivot i) (hp_bound i)
    · obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
      exact hf_mem a' (ht_bound i a' ha')

end Chain

/-- Paper, Lemma "Selection of a product chain". The bound depends only on
`m,r`; every nonempty product of the resulting block products has one color.
The assertion even permits zero input values, though the paper uses positives. -/
theorem product_chain_selection (m r : ℕ) :
    ∃ N : ℕ, ∀ color : ℕ → Fin r, ∀ x : ℕ → ℕ,
      ∃ C : Chain m, (∀ i, C.block i ⊆ Finset.range N) ∧
        ∃ c : Fin r, ∀ I : Finset (Fin m), I.Nonempty →
          color (∏ i ∈ I, ∏ j ∈ C.block i, x j) = c := by
  classical
  obtain ⟨F, hF⟩ := uniform_finite_sums_bound r m
  obtain ⟨N, hN⟩ := Ramsey.finite_size_homogeneous_bound r (2 * F) (2 * F)
  refine ⟨N, ?_⟩
  intro color x
  let indexColor : Finset ℕ → Fin r := fun A => color (∏ j ∈ A, x j)
  obtain ⟨A, hAN, hAcard, hAmono⟩ := hN indexColor
  let κ : ℕ → Fin r := fun k =>
    if hk : k ≤ 2 * F then Classical.choose (hAmono k hk) else color 1
  have hκ (B : Finset ℕ) (hBA : B ⊆ A) (hk : B.card ≤ 2 * F) :
      indexColor B = κ B.card := by
    dsimp [κ]
    rw [dif_pos hk]
    exact Classical.choose_spec (hAmono B.card hk) B hBA rfl
  obtain ⟨u, hupos, hubound, c, huc⟩ := hF (fun a => κ (2 * a))
  let q : Fin m → ℕ := fun i => 2 * u i
  have hq (i : Fin m) : 2 ≤ q i := by
    dsimp [q]
    have := hupos i
    omega
  have hqbound : (∑ i, q i) ≤ 2 * F := by
    simpa only [q, ← Finset.mul_sum] using Nat.mul_le_mul_left 2 hubound
  obtain ⟨C, hCcard, hCA⟩ := Chain.allocate_in_finset A hAcard q hq hqbound
  refine ⟨C, fun i => (hCA i).trans hAN, c, ?_⟩
  intro I hI
  let B : Finset ℕ := I.biUnion C.block
  have hBA : B ⊆ A := by
    intro a ha
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
    exact hCA i hi
  have hBcard : B.card = 2 * ∑ i ∈ I, u i := by
    rw [C.union_card, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact hCcard i
  have hBk : B.card ≤ 2 * F := (Finset.card_le_card hBA).trans_eq hAcard
  have hc : κ B.card = c := by
    rw [hBcard]
    exact huc I hI
  rw [← C.product_union I x]
  exact (hκ B hBA hBk).trans hc

end Hindman168
