import Hindman168.NativeFiniteProductCoordinateHom
import Hindman168.NativeFiniteProductLattice
import Hindman168.RoughConjugateLatticeTopology

/-! Diagonal conjugation in the ACTUAL finite product, with an exact
lattice identity. The conjugating element need not belong to any cube. -/
namespace Hindman168
attribute [local instance] nativeFiniteProductGroup
variable {G : Type*} [Group G]

def nativeFiniteProductDiagonal (ρ : G) : (n : ℕ) → nativeFiniteProduct G n
  | 0 => ρ
  | n+1 => (nativeFiniteProductDiagonal ρ n, ρ)

omit [Group G] in
theorem native_finite_product_diagonal_coordinate (ρ : G) (n : ℕ) (k : Fin (n+1)) :
    nativeFiniteProductCoordinate n (nativeFiniteProductDiagonal ρ n) k = ρ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ ?_ k
    · exact nativeFiniteProductCoordinate_last n (nativeFiniteProductDiagonal ρ (n+1))
    · intro j
      exact (nativeFiniteProductCoordinate_castSucc n _ j).trans (ih j)

theorem native_finite_product_coordinate_inv (n : ℕ) (x : nativeFiniteProduct G n)
    (k : Fin (n+1)) :
    nativeFiniteProductCoordinate n x⁻¹ k = (nativeFiniteProductCoordinate n x k)⁻¹ :=
  congrFun (map_inv (nativeFiniteProductCoordinateHom n) x) k

theorem native_finite_product_diagonal_lattice (Γ : Subgroup G) (ρ : G) (n : ℕ) :
    nativeFiniteProductLattice (roughConjugateSubgroup Γ ρ) n =
      roughConjugateSubgroup (nativeFiniteProductLattice Γ n) (nativeFiniteProductDiagonal ρ n) := by
  ext x
  rw [nativeFiniteProductLattice_mem_iff, roughConjugateSubgroup_mem_iff,
    nativeFiniteProductLattice_mem_iff]
  simp only [roughConjugateSubgroup_mem_iff, native_finite_product_coordinate_mul,
    native_finite_product_coordinate_inv, native_finite_product_diagonal_coordinate]

end Hindman168
