import Hindman168.AlternatingEnergyIndices
import Hindman168.Chain

/-! Recover finite principal coordinates of an actual Chain and locate
its common fine padding immediately before the first pivot. -/
namespace Hindman168

def principalTailPositions {n : ℕ} (e : Fin (2 * n) ↪o ℕ) (T : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun u => energyPrincipal e u ∈ T)

theorem principalTailPositions_image {n : ℕ} (e : Fin (2 * n) ↪o ℕ)
    (T : Finset ℕ) (hT : T ⊆ energyPrincipalSet e) :
    (principalTailPositions e T).image (energyPrincipal e) = T := by
  ext t
  constructor
  · rintro ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_filter.mp hu).2
  · intro ht
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp (hT ht)
    exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, rfl⟩

theorem selected_chain_coordinates {n m : ℕ} (e : Fin (2 * n) ↪o ℕ) (C : Chain m)
    (hC : ∀ i, C.block i ⊆ energyPrincipalSet e) :
    ∃ p : Fin m → Fin n, StrictMono p ∧ (∀ i, energyPrincipal e (p i) = C.pivot i) ∧
      ∀ i, (principalTailPositions e (C.tail i)).image (energyPrincipal e) = C.tail i := by
  classical
  have hp : ∀ i, ∃ u : Fin n, energyPrincipal e u = C.pivot i := by
    intro i
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp (hC i (Finset.mem_insert_self _ _))
    exact ⟨u, hu⟩
  choose p hp using hp
  refine ⟨p, ?_, hp, ?_⟩
  · intro i j hij
    apply (energyPrincipal_strictMono e).lt_iff_lt.mp
    rw [hp i, hp j]
    exact C.pivot_strictMono hij
  · intro i
    exact principalTailPositions_image e (C.tail i)
      (fun _ ht => hC i (Finset.mem_insert_of_mem ht))

theorem selected_chain_common_padding {n m : ℕ} (e : Fin (2 * n) ↪o ℕ)
    (C : Chain (m + 1)) (hC : ∀ i, C.block i ⊆ energyPrincipalSet e)
    (p : Fin (m + 1) → Fin n) (hp : ∀ i, energyPrincipal e (p i) = C.pivot i) :
    (∀ i, p 0 ≤ p i) ∧
      (∀ i, ∀ t ∈ C.tail i, t < energyPadding e (p 0)) ∧
      ∀ i, energyPadding e (p 0) ≤ energyPadding e (p i) ∧
        energyPadding e (p i) < C.pivot i := by
  have hpi : ∀ i, p 0 ≤ p i := by
    intro i
    apply (energyPrincipal_strictMono e).le_iff_le.mp
    rw [hp 0, hp i]
    exact C.pivot_strictMono.monotone (Fin.zero_le i)
  refine ⟨hpi, ?_, ?_⟩
  · intro i
    apply energyTail_before_padding e (C.tail i) (p 0)
      (fun _ ht => hC i (Finset.mem_insert_of_mem ht))
    intro t ht
    rw [hp 0]
    exact C.tails_before_pivots i 0 t ht
  · intro i
    exact ⟨energyPadding_mono e (hpi i), by simpa only [hp] using energyPadding_lt_principal e (p i)⟩

theorem selected_chain_allocated {n m : ℕ} (e : Fin (2 * n) ↪o ℕ)
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hbound : (∑ i, q i) ≤ n) :
    ∃ C : Chain m, (∀ i, (C.block i).card = q i) ∧
      (∀ i, C.block i ⊆ energyPrincipalSet e) :=
  Chain.allocate_in_finset (energyPrincipalSet e) (energyPrincipalSet_card e) q hq hbound

end Hindman168
