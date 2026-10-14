import Hindman168.Basic
import Mathlib.Combinatorics.Hindman
import Mathlib.Topology.Compactness.Compact

/-!
# Positive finite sums used in the paper's chain-selection lemma

The input is mathlib's established additive Hindman theorem. This file does
not use or assert a simultaneous sums/products theorem. Repetitions among
the auxiliary summands are permitted, as in the paper's proof.
-/

namespace Hindman168

open scoped BigOperators

def SumPattern {r m : ℕ} (color : ℕ → Fin r) (u : Fin m → ℕ) (c : Fin r) : Prop :=
  ∀ S : Finset (Fin m), S.Nonempty → color (∑ i ∈ S, u i) = c

theorem fs_positive {a : Stream' ℕ} {x : ℕ} (hx : x ∈ Hindman.FS a)
    (hpos : ∀ i, 0 < a.get i) : 0 < x := by
  revert hpos
  induction hx with
  | head' a =>
    intro hpos
    exact hpos 0
  | tail' a x _ ih =>
    intro hpos
    apply ih
    intro i
    exact hpos (i + 1)
  | cons' a x _ _ =>
    intro hpos
    exact Nat.add_pos_left (hpos 0) x

/-- Every finite coloring has a positive `m`-term monochromatic sums pattern. -/
theorem positive_finite_sums {r m : ℕ} (color : ℕ → Fin r) :
    ∃ u : Fin m → ℕ, (∀ i, 0 < u i) ∧ ∃ c : Fin r, SumPattern color u c := by
  classical
  let cells : Set (Set ℕ) := Set.range (fun c : Fin r => {x : ℕ | 0 < x ∧ color x = c})
  have hfin : cells.Finite := Set.finite_range _
  have hcov : Hindman.FS (Stream'.const (1 : ℕ)) ⊆ ⋃₀ cells := by
    intro x hx
    have hp : 0 < x := fs_positive hx (by intro i; simp)
    exact Set.mem_sUnion.mpr ⟨{y : ℕ | 0 < y ∧ color y = color x},
      Set.mem_range.mpr ⟨color x, rfl⟩, hp, rfl⟩
  obtain ⟨cell, hcell, a, ha⟩ := Hindman.FS_partition_regular
    (Stream'.const (1 : ℕ)) cells hfin hcov
  obtain ⟨c, rfl⟩ := hcell
  refine ⟨fun i => a.get i.val, ?_, c, ?_⟩
  · intro i
    exact (ha (Hindman.FS.singleton a i.val)).1
  · intro S hS
    have hnat := Hindman.FS.finsetSum a (S.image (fun i : Fin m => i.val)) (hS.image _)
    have hc := (ha hnat).2
    simpa only [Finset.sum_image Fin.val_injective.injOn] using hc

/-- For fixed auxiliary summands, being monochromatic is an open cylinder event. -/
theorem sumPattern_isOpen {r m : ℕ} [TopologicalSpace (Fin r)]
    [DiscreteTopology (Fin r)] (u : Fin m → ℕ) (c : Fin r) :
    IsOpen {color : ℕ → Fin r | SumPattern color u c} := by
  classical
  have hset : {color : ℕ → Fin r | SumPattern color u c} =
      ⋂ S : Finset (Fin m), {color : ℕ → Fin r | S.Nonempty → color (∑ i ∈ S, u i) = c} := by
    ext color
    simp [SumPattern]
  rw [hset]
  apply isOpen_iInter_of_finite
  intro S
  by_cases hS : S.Nonempty
  · have heq : {color : ℕ → Fin r | S.Nonempty → color (∑ i ∈ S, u i) = c} =
        (fun color : ℕ → Fin r => color (∑ i ∈ S, u i)) ⁻¹' {c} := by
      ext color
      simp [hS]
    rw [heq]
    exact (isOpen_discrete _).preimage (continuous_apply _)
  · simp [hS]

/-- The uniform finite bound `F(m,r)` required by the chain-selection proof.
No explicit numerical bound is asserted. Repetition among the `u i` is allowed. -/
theorem uniform_finite_sums_bound (r m : ℕ) :
    ∃ F : ℕ, ∀ color : ℕ → Fin r,
      ∃ u : Fin m → ℕ, (∀ i, 0 < u i) ∧ (∑ i, u i) ≤ F ∧
        ∃ c : Fin r, SumPattern color u c := by
  classical
  letI : TopologicalSpace (Fin r) := ⊥
  letI : DiscreteTopology (Fin r) := ⟨rfl⟩
  let U : ℕ → Set (ℕ → Fin r) := fun F =>
    {color | ∃ u : Fin m → ℕ, (∀ i, 0 < u i) ∧ (∑ i, u i) ≤ F ∧
      ∃ c : Fin r, SumPattern color u c}
  have hopen : ∀ F, IsOpen (U F) := by
    intro F
    apply isOpen_iff_mem_nhds.mpr
    intro color hcolor
    obtain ⟨u, hpos, hbound, c, hmono⟩ := hcolor
    apply Filter.mem_of_superset ((sumPattern_isOpen u c).mem_nhds hmono)
    intro color' hmono'
    exact ⟨u, hpos, hbound, c, hmono'⟩
  have hcov : (Set.univ : Set (ℕ → Fin r)) ⊆ ⋃ F, U F := by
    intro color _
    obtain ⟨u, hpos, c, hmono⟩ := positive_finite_sums (m := m) color
    exact Set.mem_iUnion.mpr ⟨∑ i, u i, u, hpos, le_rfl, c, hmono⟩
  have hdir : Directed (· ⊆ ·) U := by
    intro F G
    refine ⟨max F G, ?_, ?_⟩
    · intro color hcolor
      obtain ⟨u, hpos, hbound, c, hmono⟩ := hcolor
      exact ⟨u, hpos, hbound.trans (le_max_left F G), c, hmono⟩
    · intro color hcolor
      obtain ⟨u, hpos, hbound, c, hmono⟩ := hcolor
      exact ⟨u, hpos, hbound.trans (le_max_right F G), c, hmono⟩
  obtain ⟨F, hF⟩ := (isCompact_univ : IsCompact (Set.univ : Set (ℕ → Fin r))).elim_directed_cover
    U hopen hcov hdir
  exact ⟨F, fun color => hF (Set.mem_univ color)⟩

end Hindman168
