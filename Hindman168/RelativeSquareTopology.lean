import Hindman168.RelativeSquareSubgroup
import Mathlib.Topology.Algebra.Group.Basic

/-! Actual relative-square closedness for closed original layers. This
does not assert restricted-lattice compactness or rationality. -/

namespace Hindman168
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem relative_square_closed (H N : Subgroup G) [N.Normal]
    (hH : IsClosed (H : Set G)) (hN : IsClosed (N : Set G)) :
    IsClosed (relativeSquareSubgroup H N : Set (G × G)) := by
  have he : (relativeSquareSubgroup H N : Set (G × G)) =
      {p : G × G | p.1 ∈ H} ∩ {p : G × G | p.2 ∈ H} ∩
        {p : G × G | p.2⁻¹*p.1 ∈ N} := by
    ext p
    exact (relative_square_mem_iff H N p).trans and_assoc.symm
  rw [he]
  exact ((hH.preimage continuous_fst).inter (hH.preimage continuous_snd)).inter
    (hN.preimage (continuous_snd.inv.mul continuous_fst))

end Hindman168
