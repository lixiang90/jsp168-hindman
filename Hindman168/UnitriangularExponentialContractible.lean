import Hindman168.UnitriangularExponentialTopology
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! Connectedness and simple connectedness of the actual real matrix group
follow from its proved global exponential homeomorphism to a real linear
space. These are topological conclusions, not a smooth Lie-group structure
or a comparison theorem for arbitrary nilpotent Lie groups. -/

namespace Hindman168

variable {n : ℕ}

 theorem unitriangular_contractible : ContractibleSpace (Unitriangular n ℝ) :=
  (unitriangularExponentialHomeomorph (n := n) (R := ℝ)).symm.contractibleSpace

instance (n : ℕ) : ContractibleSpace (Unitriangular n ℝ) := unitriangular_contractible

 theorem unitriangular_simplyConnected : SimplyConnectedSpace (Unitriangular n ℝ) :=
  inferInstance

 theorem unitriangular_pathConnected : PathConnectedSpace (Unitriangular n ℝ) := inferInstance

 theorem unitriangular_connected : ConnectedSpace (Unitriangular n ℝ) := inferInstance

end Hindman168
