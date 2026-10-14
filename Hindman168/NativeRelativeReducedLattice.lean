import Hindman168.NativeRelativeTerminalRational
import Hindman168.NativeRelativeTerminalSubgroup
import Hindman168.NativeCentralSubspaceQuotientLattice
import Hindman168.SubgroupQuotientLatticeTransport

/-! ACTUAL original relative restricted lattice image in quotient by
SAME terminal diagonal is discrete/cocompact/closed; all inputs are proved. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

theorem native_relative_reduced_lattice_discrete {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := native_relative_terminal_subgroup_normal D d hd
    DiscreteTopology ((nativeRelativeSquareData D d hd 1).Γ.map
      (QuotientGroup.mk' (nativeRelativeTerminalSubgroup D d hd))) := by
  letI := native_relative_terminal_subgroup_normal D d hd
  have h := nativeCentralSubspaceQuotient_lattice_image_discrete
    (E := (nativeRelativeSquareData D d hd 1).E) (I := (nativeRelativeSquareData D d hd 1).I)
    (nativeRelativeSquareData D d hd 1).Γ (nativeRelativeTerminalModel D d hd)
    (native_relative_terminal_model_le_center D d hd) (native_relative_terminal_model_rational D d hd)
  exact subgroup_quotient_lattice_discrete_of_eq _ _ _
    (native_relative_terminal_subgroup_central_eq D d hd) h

theorem native_relative_reduced_lattice_cocompact {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := native_relative_terminal_subgroup_normal D d hd
    CompactSpace (((nativeRelativeSquareData D d hd 1).G ⧸ nativeRelativeTerminalSubgroup D d hd) ⧸
      (nativeRelativeSquareData D d hd 1).Γ.map (QuotientGroup.mk' (nativeRelativeTerminalSubgroup D d hd))) := by
  letI := native_relative_terminal_subgroup_normal D d hd
  exact normalQuotient_lattice_image_cocompact _ _

theorem native_relative_terminal_subgroup_closed {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    IsClosed (nativeRelativeTerminalSubgroup D d hd : Set (nativeRelativeSquareData D d hd 1).G) := by
  have h := nativeCentralSubspaceSubgroup_closed (I := (nativeRelativeSquareData D d hd 1).I)
    (nativeRelativeTerminalModel D d hd) (native_relative_terminal_model_le_center D d hd)
  exact Eq.mp (congrArg (fun K : Subgroup (nativeRelativeSquareData D d hd 1).G =>
    IsClosed (K : Set (nativeRelativeSquareData D d hd 1).G))
    (native_relative_terminal_subgroup_central_eq D d hd)) h

theorem native_relative_reduced_lattice_closed {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := native_relative_terminal_subgroup_normal D d hd
    IsClosed (((nativeRelativeSquareData D d hd 1).Γ.map
      (QuotientGroup.mk' (nativeRelativeTerminalSubgroup D d hd))) :
        Set ((nativeRelativeSquareData D d hd 1).G ⧸ nativeRelativeTerminalSubgroup D d hd)) := by
  letI := native_relative_terminal_subgroup_normal D d hd
  letI : IsClosed (nativeRelativeTerminalSubgroup D d hd : Set (nativeRelativeSquareData D d hd 1).G) :=
    native_relative_terminal_subgroup_closed D d hd
  letI := native_relative_reduced_lattice_discrete D d hd
  exact Subgroup.isClosed_of_discrete

end Hindman168
