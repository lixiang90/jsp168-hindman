import Hindman168.NativeFiniteProductCoordinates
import Hindman168.ProductLatticeGeometry

/-! The specified lattice in the actual nonempty finite product.
Discreteness and cocompactness come from the original specified lattice. -/

namespace Hindman168

attribute [local instance] nativeFiniteProductGroup nativeFiniteProductTopologicalSpace

variable {G : Type*} [Group G]

def nativeFiniteProductLattice (Γ : Subgroup G) : (n : ℕ) → Subgroup (nativeFiniteProduct G n)
  | 0 => Γ
  | n + 1 => (nativeFiniteProductLattice Γ n).prod Γ

theorem nativeFiniteProductLattice_mem_iff (Γ : Subgroup G) (n : ℕ)
    (g : nativeFiniteProduct G n) :
    g ∈ nativeFiniteProductLattice Γ n ↔ ∀ i, nativeFiniteProductCoordinate n g i ∈ Γ := by
  induction n with
  | zero =>
    constructor
    · intro hg i; exact hg
    · intro hg; exact hg 0
  | succ n ih =>
    change g.1 ∈ nativeFiniteProductLattice Γ n ∧ g.2 ∈ Γ ↔ _
    rw [ih]
    constructor
    · rintro ⟨h, hlast⟩ i
      refine Fin.lastCases ?_ ?_ i
      · simpa only [nativeFiniteProductCoordinate_last] using hlast
      · intro j
        simpa only [nativeFiniteProductCoordinate_castSucc] using h j
    · intro h
      exact ⟨fun j => by simpa only [nativeFiniteProductCoordinate_castSucc] using h j.castSucc,
        by simpa only [nativeFiniteProductCoordinate_last] using h (Fin.last (n + 1))⟩

variable [TopologicalSpace G]

theorem nativeFiniteProduct_topologicalGroup [IsTopologicalGroup G] :
    (n : ℕ) → IsTopologicalGroup (nativeFiniteProduct G n)
  | 0 => inferInstanceAs (IsTopologicalGroup G)
  | n + 1 => by
    letI := nativeFiniteProduct_topologicalGroup n
    exact inferInstanceAs (IsTopologicalGroup (nativeFiniteProduct G n × G))

theorem nativeFiniteProductLattice_discrete (Γ : Subgroup G) [DiscreteTopology Γ] :
    (n : ℕ) → DiscreteTopology (nativeFiniteProductLattice Γ n)
  | 0 => inferInstanceAs (DiscreteTopology Γ)
  | n + 1 => by
    letI := nativeFiniteProductLattice_discrete Γ n
    exact productLattice_discrete (nativeFiniteProductLattice Γ n) Γ

theorem nativeFiniteProductLattice_cocompact [IsTopologicalGroup G]
    (Γ : Subgroup G) [CompactSpace (G ⧸ Γ)] :
    (n : ℕ) → CompactSpace (nativeFiniteProduct G n ⧸ nativeFiniteProductLattice Γ n)
  | 0 => inferInstanceAs (CompactSpace (G ⧸ Γ))
  | n + 1 => by
    letI := nativeFiniteProduct_topologicalGroup (G := G) n
    letI := nativeFiniteProductLattice_cocompact Γ n
    exact productLattice_quotient_compact (nativeFiniteProductLattice Γ n) Γ

end Hindman168
