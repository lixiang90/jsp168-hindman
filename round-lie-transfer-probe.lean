import Hindman168.UnitriangularLieGroup
import Hindman168.StrictMatrixSmoothProjection
open scoped Matrix.Norms.Elementwise Manifold ContDiff
namespace Hindman168
variable (n : ℕ)
#check NormedAddCommGroup.toMetricSpace
example : (inferInstance : TopologicalSpace (StrictUpperTriangular n ℝ)) =
    (inferInstance : NormedAddCommGroup (StrictUpperTriangular n ℝ)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
  rfl
local instance strictTopology (n : ℕ) : TopologicalSpace (StrictUpperTriangular n ℝ) :=
  (inferInstance : NormedAddCommGroup (StrictUpperTriangular n ℝ)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
local instance strictSelf (n : ℕ) :
    ChartedSpace (StrictUpperTriangular n ℝ) (StrictUpperTriangular n ℝ) :=
  chartedSpaceSelf (StrictUpperTriangular n ℝ)
#check (ContMDiff 𝓘(ℝ, StrictUpperTriangular n ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ) ∞
  (unitriangularExponential : StrictUpperTriangular n ℝ → Unitriangular n ℝ))
end Hindman168
