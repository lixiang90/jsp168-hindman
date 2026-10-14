import Hindman168.NativeRationalFilteredGroupGeometry

/-! A TRUE degree-one rational filtration forces the ORIGINAL group to be
abelian. Reclassifying its PROVED step bound preserves every actual datum
field, including the original model/group/lattice/metric. -/

namespace Hindman168
open scoped Manifold ContDiff commutatorElement
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_degree_one_commutative {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D 1) : IsMulCommutative D.G := by
  refine ⟨⟨fun g h => ?_⟩⟩
  apply commutatorElement_eq_one_iff_mul_comm.mp
  have hg : g ∈ nativeRationalFilteredGroupLayer D F 1 := by
    rw [native_rational_filtered_group_one]; exact Subgroup.mem_top _
  have hh : h ∈ nativeRationalFilteredGroupLayer D F 1 := by
    rw [native_rational_filtered_group_one]; exact Subgroup.mem_top _
  have hm := (native_rational_filtered_group_conditions D F).commutator_mem 1 1 g hg h hh
  rw [native_rational_filtered_group_terminal D F,Subgroup.mem_bot] at hm
  exact hm

theorem native_rational_degree_one_nilpotency {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D 1) :
    Group.nilpotencyClass D.G ≤ 1 :=
  Group.IsNilpotent.nilpotencyClass_le_one_iff.mpr (native_rational_degree_one_commutative D F)

theorem native_rational_degree_one_bracket_zero {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D 1) (v w : D.E) :
    nativeLieAdjointDifferential (I := D.I) (G := D.G) v w = 0 := by
  have hv : v ∈ F.layer 1 := by rw [F.one]; exact Submodule.mem_top
  have hw : w ∈ F.layer 1 := by rw [F.one]; exact Submodule.mem_top
  have hm := F.bracket 1 1 v w hv hw
  rw [F.terminal,Submodule.mem_bot] at hm
  exact hm

noncomputable def nativeRationalDegreeOneData {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D 1) : NativeNilmanifoldData.{u} 1 where
  E := D.E
  H := D.H
  I := D.I
  G := D.G
  step_le := native_rational_degree_one_nilpotency D F
  Γ := D.Γ
  metric := D.metric
  metric_quotientMap := D.metric_quotientMap

theorem native_rational_degree_one_original_lattice {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D 1) :
    (nativeRationalDegreeOneData D F).Γ = D.Γ := rfl

theorem native_rational_degree_one_original_metric {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D 1) :
    (nativeRationalDegreeOneData D F).metric = D.metric := rfl

end Hindman168
