import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Compactness.Compact
import Lean.Elab.Tactic.Omega

/-!
# Hypergraph Ramsey input for product-chain selection

This is the usual induction-on-uniformity proof of infinite Ramsey's theorem:
successively choose a head and an infinite homogeneous reservoir, then pass to
an infinite fiber of the head colors. The same proof strategy appears in
Bhavik Mehta's Lean 3 `inf_ramsey.lean`:
https://github.com/b-mehta/combinatorics/blob/extras/src/inf_ramsey.lean

The recursion and proofs here are written for the pinned Lean 4 environment.
Compactness then supplies the finite bound; no numerical Ramsey bound is used.
-/

namespace Hindman168.Ramsey

/-- Homogeneity on all `k`-element subsets of an ambient set. -/
def Homogeneous {r : ℕ} (color : Finset ℕ → Fin r) (k : ℕ)
    (S : Set ℕ) (c : Fin r) : Prop :=
  ∀ A : Finset ℕ, (↑A : Set ℕ) ⊆ S → A.card = k → color A = c

/-- A head with an infinite reservoir on which all extensions have one color. -/
private structure Reservoir {r : ℕ} (color : Finset ℕ → Fin r) (k : ℕ)
    (S : Set ℕ) where
  head : ℕ
  rest : Set ℕ
  shade : Fin r
  head_mem : head ∈ S
  rest_subset : rest ⊆ S
  rest_infinite : rest.Infinite
  above : ∀ x ∈ rest, head < x
  mono : Homogeneous (fun A => color (insert head A)) k rest shade

/-- Infinite Ramsey for every uniformity and every finite palette. -/
theorem infinite_homogeneous {r : ℕ} (k : ℕ) (color : Finset ℕ → Fin r)
    (S : Set ℕ) (hS : S.Infinite) :
    ∃ T : Set ℕ, T ⊆ S ∧ T.Infinite ∧ ∃ c : Fin r, Homogeneous color k T c := by
  classical
  induction k generalizing color S with
  | zero =>
    refine ⟨S, Set.Subset.rfl, hS, color ∅, ?_⟩
    intro A _ hA
    have hAe : A = ∅ := Finset.card_eq_zero.mp hA
    simp [hAe]
  | succ k ih =>
    have hstate : ∀ U : Set ℕ, U ⊆ S → U.Infinite →
        ∃ t : Reservoir color k S, t.head ∈ U ∧ t.rest ⊆ U := by
      intro U hUS hU
      obtain ⟨a, ha⟩ := hU.nonempty
      let V : Set ℕ := U \ (↑(Finset.range (a + 1)) : Set ℕ)
      have hV : V.Infinite := hU.sdiff (Finset.finite_toSet _)
      obtain ⟨T, hTV, hT, c, hc⟩ := ih (fun A => color (insert a A)) V hV
      have hTU : T ⊆ U := fun x hx => (hTV hx).1
      have hgt : ∀ x ∈ T, a < x := by
        intro x hx
        have hn : x ∉ Finset.range (a + 1) := (hTV hx).2
        simp only [Finset.mem_range] at hn
        omega
      exact ⟨⟨a, T, c, hUS ha, hTU.trans hUS, hT, hgt, hc⟩, ha, hTU⟩
    obtain ⟨initial, _, _⟩ := hstate S Set.Subset.rfl hS
    have hnext : ∀ t : Reservoir color k S,
        ∃ u : Reservoir color k S, u.head ∈ t.rest ∧ u.rest ⊆ t.rest :=
      fun t => hstate t.rest t.rest_subset t.rest_infinite
    let next (t : Reservoir color k S) := Classical.choose (hnext t)
    have hnext_spec (t : Reservoir color k S) :
        (next t).head ∈ t.rest ∧ (next t).rest ⊆ t.rest :=
      Classical.choose_spec (hnext t)
    let f : ℕ → Reservoir color k S := fun n => Nat.rec initial (fun _ t => next t) n
    have hf (i : ℕ) : f (i + 1) = next (f i) := rfl
    have hstep (i : ℕ) : (f (i + 1)).head ∈ (f i).rest ∧
        (f (i + 1)).rest ⊆ (f i).rest := by
      rw [hf]
      exact hnext_spec (f i)
    have hmono : StrictMono (fun i => (f i).head) :=
      strictMono_nat_of_lt_succ (fun i => (f i).above _ (hstep i).1)
    have hrest : Antitone (fun i => (f i).rest) :=
      antitone_nat_of_succ_le (fun i => (hstep i).2)
    have hhead (i j : ℕ) (hij : i < j) : (f j).head ∈ (f i).rest := by
      cases j with
      | zero => omega
      | succ j => exact hrest (by omega : i ≤ j) (hstep j).1
    obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber (fun i : ℕ => (f i).shade)
    let I : Set ℕ := {i | (f i).shade = c}
    have hI : I.Infinite := Set.infinite_coe_iff.mp hc
    let T : Set ℕ := (fun i => (f i).head) '' I
    refine ⟨T, ?_, hI.image hmono.injective.injOn, c, ?_⟩
    · rintro x ⟨i, _, rfl⟩
      exact (f i).head_mem
    · intro A hAT hcard
      have hA : A.Nonempty := Finset.card_pos.mp (by omega)
      let a := A.min' hA
      have haA : a ∈ A := A.min'_mem hA
      obtain ⟨i, hi, hai⟩ := hAT haA
      change (f i).head = a at hai
      have hsub : (↑(A.erase a) : Set ℕ) ⊆ (f i).rest := by
        intro x hx
        obtain ⟨hne, hxA⟩ := Finset.mem_erase.mp hx
        obtain ⟨j, _, hj⟩ := hAT hxA
        have hax : a < x := lt_of_le_of_ne (A.min'_le x hxA) (Ne.symm hne)
        have hij : i < j := hmono.lt_iff_lt.mp (by simpa [hai, hj] using hax)
        simpa [hj] using hhead i j hij
      have hkc : (A.erase a).card = k := by
        rw [Finset.card_erase_of_mem haA, hcard]
        omega
      have hres : color (insert (f i).head (A.erase a)) = (f i).shade :=
        (f i).mono (A.erase a) hsub hkc
      have hshade : (f i).shade = c := hi
      rw [hai, Finset.insert_erase haA, hshade] at hres
      exact hres

/-- Each subset size up to `K` has its own common color. -/
def SizeHomogeneous {r : ℕ} (color : Finset ℕ → Fin r) (K : ℕ) (S : Set ℕ) : Prop :=
  ∀ k ≤ K, ∃ c : Fin r, Homogeneous color k S c

theorem Homogeneous.mono {r k : ℕ} {color : Finset ℕ → Fin r}
    {S T : Set ℕ} {c : Fin r} (h : Homogeneous color k S c) (hTS : T ⊆ S) :
    Homogeneous color k T c :=
  fun A hAT hcard => h A (hAT.trans hTS) hcard

theorem SizeHomogeneous.mono {r K : ℕ} {color : Finset ℕ → Fin r}
    {S T : Set ℕ} (h : SizeHomogeneous color K S) (hTS : T ⊆ S) :
    SizeHomogeneous color K T := by
  intro k hk
  obtain ⟨c, hc⟩ := h k hk
  exact ⟨c, hc.mono hTS⟩

/-- Successive Ramsey refinements make every size up to `K` homogeneous. -/
theorem infinite_size_homogeneous {r : ℕ} (K : ℕ) (color : Finset ℕ → Fin r)
    (S : Set ℕ) (hS : S.Infinite) :
    ∃ T : Set ℕ, T ⊆ S ∧ T.Infinite ∧ SizeHomogeneous color K T := by
  classical
  induction K with
  | zero =>
    refine ⟨S, Set.Subset.rfl, hS, ?_⟩
    intro k hk
    have hk0 : k = 0 := by omega
    refine ⟨color ∅, ?_⟩
    intro A _ hA
    have he : A = ∅ := Finset.card_eq_zero.mp (by omega)
    simp [he]
  | succ K ih =>
    obtain ⟨T, hTS, hT, ht⟩ := ih
    obtain ⟨U, hUT, hU, c, hc⟩ := infinite_homogeneous (K + 1) color T hT
    refine ⟨U, hUT.trans hTS, hU, ?_⟩
    intro k hk
    by_cases hkK : k ≤ K
    · obtain ⟨d, hd⟩ := ht k hkK
      exact ⟨d, hd.mono hUT⟩
    · have he : k = K + 1 := by omega
      exact ⟨c, he ▸ hc⟩

/-- Homogeneity on a fixed finite set is an open cylinder condition. -/
theorem homogeneous_isOpen {r : ℕ} [TopologicalSpace (Fin r)]
    [DiscreteTopology (Fin r)] (k : ℕ) (A : Finset ℕ) (c : Fin r) :
    IsOpen {color : Finset ℕ → Fin r | Homogeneous color k (↑A) c} := by
  classical
  have heq : {color : Finset ℕ → Fin r | Homogeneous color k (↑A) c} =
      ⋂ B : A.powerset, {color : Finset ℕ → Fin r | B.val.card = k → color B.val = c} := by
    ext color
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h B
      exact h B.val (Finset.mem_powerset.mp B.property)
    · intro h B hBA hcard
      exact h ⟨B, Finset.mem_powerset.mpr hBA⟩ hcard
  rw [heq]
  apply isOpen_iInter_of_finite
  intro B
  by_cases hB : B.val.card = k
  · have he : {color : Finset ℕ → Fin r | B.val.card = k → color B.val = c} =
        (fun color : Finset ℕ → Fin r => color B.val) ⁻¹' {c} := by
      ext color
      simp [hB]
    rw [he]
    exact (isOpen_discrete _).preimage (continuous_apply B.val)
  · simp [hB]

theorem sizeHomogeneous_isOpen {r : ℕ} [TopologicalSpace (Fin r)]
    [DiscreteTopology (Fin r)] (K : ℕ) (A : Finset ℕ) :
    IsOpen {color : Finset ℕ → Fin r | SizeHomogeneous color K (↑A)} := by
  classical
  have heq : {color : Finset ℕ → Fin r | SizeHomogeneous color K (↑A)} =
      ⋂ k : Fin (K + 1), ⋃ c : Fin r,
        {color : Finset ℕ → Fin r | Homogeneous color k.val (↑A) c} := by
    ext color
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro h k
      exact h k.val (by omega)
    · intro h k hk
      exact h ⟨k, by omega⟩
  rw [heq]
  apply isOpen_iInter_of_finite
  intro k
  exact isOpen_iUnion (fun c => homogeneous_isOpen k.val A c)

/-- A uniform finite interval contains an `n`-element set whose subset color
depends only on cardinality, for cardinalities at most `K`. -/
theorem finite_size_homogeneous_bound (r K n : ℕ) :
    ∃ N : ℕ, ∀ color : Finset ℕ → Fin r,
      ∃ A : Finset ℕ, (↑A : Set ℕ) ⊆ ↑(Finset.range N) ∧ A.card = n ∧
        SizeHomogeneous color K (↑A) := by
  classical
  letI : TopologicalSpace (Fin r) := ⊥
  letI : DiscreteTopology (Fin r) := ⟨rfl⟩
  let U : ℕ → Set (Finset ℕ → Fin r) := fun N =>
    {color | ∃ A : Finset ℕ, (↑A : Set ℕ) ⊆ ↑(Finset.range N) ∧ A.card = n ∧
      SizeHomogeneous color K (↑A)}
  have hopen : ∀ N, IsOpen (U N) := by
    intro N
    apply isOpen_iff_mem_nhds.mpr
    intro color hcolor
    obtain ⟨A, hAN, hcard, hmono⟩ := hcolor
    apply Filter.mem_of_superset ((sizeHomogeneous_isOpen K A).mem_nhds hmono)
    intro color' hmono'
    exact ⟨A, hAN, hcard, hmono'⟩
  have hcov : (Set.univ : Set (Finset ℕ → Fin r)) ⊆ ⋃ N, U N := by
    intro color _
    obtain ⟨T, _, hT, hmono⟩ := infinite_size_homogeneous K color Set.univ Set.infinite_univ
    obtain ⟨A, hAT, hcard⟩ := hT.exists_subset_card_eq n
    refine Set.mem_iUnion.mpr ⟨A.sup id + 1, A, ?_, hcard, hmono.mono hAT⟩
    intro x hx
    apply Finset.mem_range.mpr
    have hxle : x ≤ A.sup id := Finset.le_sup (f := id) hx
    omega
  have hdir : Directed (· ⊆ ·) U := by
    intro N M
    refine ⟨max N M, ?_, ?_⟩
    · intro color hcolor
      obtain ⟨A, hAN, hcard, hmono⟩ := hcolor
      exact ⟨A, hAN.trans (Finset.range_mono (le_max_left N M)), hcard, hmono⟩
    · intro color hcolor
      obtain ⟨A, hAM, hcard, hmono⟩ := hcolor
      exact ⟨A, hAM.trans (Finset.range_mono (le_max_right N M)), hcard, hmono⟩
  obtain ⟨N, hN⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (Finset ℕ → Fin r))).elim_directed_cover
      U hopen hcov hdir
  exact ⟨N, fun color => hN (Set.mem_univ color)⟩

end Hindman168.Ramsey
