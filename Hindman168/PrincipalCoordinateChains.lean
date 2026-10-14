import Hindman168.SelectedPrincipalScales

/-! Chains on the relabeled principal coordinates lift to the actual
master chain, preserving every tail, pivot and block. -/

namespace Hindman168
open scoped BigOperators Classical

structure PrincipalCoordinateChain (n m : ℕ) where
  tail : Fin m → Finset (Fin n)
  pivot : Fin m → Fin n
  tail_nonempty : ∀ i, (tail i).Nonempty
  tail_before : ∀ i j, i < j → ∀ a ∈ tail i, ∀ b ∈ tail j, a < b
  tails_before_pivots : ∀ i j, ∀ a ∈ tail i, a < pivot j
  pivot_strictMono : StrictMono pivot

namespace PrincipalCoordinateChain

def block {n m : ℕ} (C : PrincipalCoordinateChain n m) (i : Fin m) : Finset (Fin n) :=
  insert (C.pivot i) (C.tail i)

def lift {n m : ℕ} (C : PrincipalCoordinateChain n m) (e : Fin (2*n) ↪o ℕ) : Chain m where
  tail := fun i => (C.tail i).image (energyPrincipal e)
  pivot := fun i => energyPrincipal e (C.pivot i)
  tail_nonempty := fun i => (C.tail_nonempty i).image _
  tail_before := by
    intro i j hij a ha b hb
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    exact (energyPrincipal_strictMono e) (C.tail_before i j hij a' ha' b' hb')
  tails_before_pivots := by
    intro i j a ha
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    exact (energyPrincipal_strictMono e) (C.tails_before_pivots i j a' ha')
  pivot_strictMono := (energyPrincipal_strictMono e).comp C.pivot_strictMono

theorem lift_block {n m : ℕ} (C : PrincipalCoordinateChain n m)
    (e : Fin (2*n) ↪o ℕ) (i : Fin m) :
    (C.lift e).block i = (C.block i).image (energyPrincipal e) := by
  simp only [Chain.block, lift, block, Finset.image_insert]

theorem lift_selected {n m : ℕ} (C : PrincipalCoordinateChain n m)
    (e : Fin (2*n) ↪o ℕ) : ∀ i, (C.lift e).block i ⊆ energyPrincipalSet e := by
  intro i
  rw [lift_block]
  intro j hj
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

theorem lift_range {n m M : ℕ} (C : PrincipalCoordinateChain n m)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) :
    ∀ i, (C.lift e).block i ⊆ Finset.range M := by
  intro i
  rw [lift_block]
  exact selectedPrincipal_image_range e heM _

theorem lift_tail_positions {n m : ℕ} (C : PrincipalCoordinateChain n m)
    (e : Fin (2*n) ↪o ℕ) (i : Fin m) :
    principalTailPositions e ((C.lift e).tail i) = C.tail i := by
  ext k
  simp only [principalTailPositions, Finset.mem_filter, Finset.mem_univ, true_and,
    lift, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, he⟩
    exact (energyPrincipal_strictMono e).injective he ▸ hj
  · intro hk
    exact ⟨k, hk, rfl⟩

theorem lift_pivot_coordinates {n m : ℕ} (C : PrincipalCoordinateChain n m)
    (e : Fin (2*n) ↪o ℕ) (p : Fin m → Fin n)
    (hp : ∀ i, energyPrincipal e (p i) = (C.lift e).pivot i) : p = C.pivot := by
  funext i
  exact (energyPrincipal_strictMono e).injective (hp i)

end PrincipalCoordinateChain
end Hindman168
