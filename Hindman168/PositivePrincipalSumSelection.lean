import Hindman168.PrincipalCoordinateProducts
import Mathlib.Tactic

/-!
# The finite product-chain selector on the actual principal coordinates

This transports the already proved Lemma 2.5 into the finite coordinate
chain type used by the prediction counts. The set of candidate chains is
finite, so a sum over all candidates does not require a fixed samplewise
choice.
-/

namespace Hindman168
open scoped BigOperators Classical

instance {n m : ℕ} : Finite (PrincipalCoordinateChain n m) := by
  apply Finite.of_injective (fun C : PrincipalCoordinateChain n m => (C.tail, C.pivot))
  intro C D h
  cases C
  cases D
  cases Prod.mk.inj h with
  | intro ht hp => cases ht; cases hp; rfl

noncomputable instance {n m : ℕ} : Fintype (PrincipalCoordinateChain n m) := Fintype.ofFinite _

/-- Restrict a natural-index chain contained in `[0,n)` to `Fin n`. -/
noncomputable def principalChainOfRange {n m : ℕ} (C : Chain m)
    (hC : ∀ i, C.block i ⊆ Finset.range n) : PrincipalCoordinateChain n m where
  tail i := Finset.univ.filter (fun k : Fin n => k.val ∈ C.tail i)
  pivot i := ⟨C.pivot i, Finset.mem_range.mp (hC i (Finset.mem_insert_self _ _))⟩
  tail_nonempty i := by
    obtain ⟨k, hk⟩ := C.tail_nonempty i
    have hkn : k < n := Finset.mem_range.mp (hC i (Finset.mem_insert_of_mem hk))
    exact ⟨⟨k, hkn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  tail_before i j hij x hx y hy :=
    C.tail_before i j hij x.val (Finset.mem_filter.mp hx).2 y.val (Finset.mem_filter.mp hy).2
  tails_before_pivots i j x hx :=
    C.tails_before_pivots i j x.val (Finset.mem_filter.mp hx).2
  pivot_strictMono i j hij := C.pivot_strictMono hij

theorem principalChainOfRange_block_image {n m : ℕ} (C : Chain m)
    (hC : ∀ i, C.block i ⊆ Finset.range n) (i : Fin m) :
    ((principalChainOfRange C hC).block i).image Fin.val = C.block i := by
  ext k
  simp only [PrincipalCoordinateChain.block, principalChainOfRange, Finset.image_insert,
    Finset.mem_insert, Chain.block]
  constructor
  · rintro (hk | hk)
    · exact Or.inl hk
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      exact Or.inr (Finset.mem_filter.mp hj).2
  · rintro (hk | hk)
    · exact Or.inl hk
    · right
      have hkn : k < n := Finset.mem_range.mp (hC i (Finset.mem_insert_of_mem hk))
      exact Finset.mem_image.mpr ⟨⟨k, hkn⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, rfl⟩

/-- Exact principal-coordinate form of the already proved product-chain
selection lemma, valid for every list of natural inputs. -/
theorem principal_product_chain_selection (m r : ℕ) :
    ∃ n : ℕ, ∀ χ : ℕ → Fin r, ∀ x : Fin n → ℕ,
      ∃ C : PrincipalCoordinateChain n m, ∃ κ : Fin r,
        ∀ J : Finset (Fin m), J.Nonempty →
          χ (∏ i ∈ J, C.sampleProducts x i) = κ := by
  obtain ⟨n, hn⟩ := product_chain_selection m r
  refine ⟨n, ?_⟩
  intro χ x
  let y : ℕ → ℕ := fun k => if hk : k < n then x ⟨k, hk⟩ else 0
  obtain ⟨C, hC, κ, hmono⟩ := hn χ y
  refine ⟨principalChainOfRange C hC, κ, ?_⟩
  intro J hJ
  have hprod (i : Fin m) : (principalChainOfRange C hC).sampleProducts x i =
      ∏ k ∈ C.block i, y k := by
    rw [← principalChainOfRange_block_image C hC i,
      Finset.prod_image Fin.val_injective.injOn]
    apply Finset.prod_congr rfl
    intro k _
    simp only [y, dif_pos k.isLt, Fin.eta]
  simpa only [hprod] using hmono J hJ

end Hindman168
