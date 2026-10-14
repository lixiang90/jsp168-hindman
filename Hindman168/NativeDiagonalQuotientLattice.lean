import Hindman168.NativeDiagonalCenterRational
import Hindman168.NativeDiagonalCenterSubgroupEquality
import Hindman168.NativeCentralSubspaceQuotientLattice
import Hindman168.SubgroupQuotientLatticeTransport
import Hindman168.NativeFourierPairFactor
import Hindman168.DiagonalCenterClosed

/-! Actual ORIGINAL product lattice image in ACTUAL diagonal-center group
quotient is discrete and cocompact. Rational/center hypotheses are proved. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal
attribute [local instance] diagonal_center_normal

theorem native_diagonal_quotient_lattice_discrete {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    DiscreteTopology ((D.Γ.prod D.Γ).map (QuotientGroup.mk' (diagonalCenterSubgroup D.G))) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  letI := productLattice_discrete D.Γ D.Γ
  letI := productLattice_quotient_compact D.Γ D.Γ
  have h := nativeCentralSubspaceQuotient_lattice_image_discrete (E := D.E × D.E)
    (I := D.I.prod D.I) (G := D.G × D.G) (D.Γ.prod D.Γ)
    (nativeDiagonalCenterModel D) (native_diagonal_center_model_le D) (native_diagonal_center_model_rational D)
  exact subgroup_quotient_lattice_discrete_of_eq _ (diagonalCenterSubgroup D.G) (D.Γ.prod D.Γ)
    (native_diagonal_center_exponential_subgroup D) h

theorem native_diagonal_quotient_lattice_cocompact {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    CompactSpace (nativeDiagonalFactorSpace D) := native_diagonal_factor_compact D

theorem native_diagonal_quotient_lattice_closed {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    IsClosed (((D.Γ.prod D.Γ).map (QuotientGroup.mk' (diagonalCenterSubgroup D.G))) :
      Set ((D.G × D.G) ⧸ diagonalCenterSubgroup D.G)) := by
  letI : IsClosed ((diagonalCenterSubgroup D.G) : Set (D.G × D.G)) := diagonal_center_closed D.G
  letI := native_diagonal_quotient_lattice_discrete D
  exact Subgroup.isClosed_of_discrete

end Hindman168
