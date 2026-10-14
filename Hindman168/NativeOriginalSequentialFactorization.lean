import Hindman168.NativeSequentialAdaptedFactorization
import Hindman168.NativeOriginalLinearOrbitAdapted

/-! Instantiate the sequential algebraic factorization at the ORIGINAL
lower-central filtration, with terminal index s and no degree-dependent
stretch. In particular it applies to every sequence of genuine left-linear
orbits, including the original all-target native joint group. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeOriginalSubgroupLieFiltration {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) : NativeRationalSubgroupFiltration D s where
  layer := roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1
  antitone := rough_native_stretched_lie_antitone 1 (by omega)
  initial := (rough_native_stretched_lie_initial 1 (by omega) 0 (by omega)).trans
    (rough_native_stretched_lie_initial 1 (by omega) 1 (by omega)).symm
  bracket := fun _ _ _ _ hv hw => rough_native_stretched_lie_bracket 1 (by omega) hv hw
  rational := fun i => nativeLieLowerCentralModel_lattice_rational (I := D.I) D.Γ ((i ⌈/⌉ 1)-1)
  terminal := by simpa only [Nat.mul_one] using rough_native_stretched_lie_terminal 1 (by omega) D.step_le

theorem native_original_linear_sequence_algebraic_factorization {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) (g a : ℕ → D.G) :
    NativeSequentialAlgebraicFactorization D (nativeOriginalSubgroupLieFiltration D) L
      (fun n => nativeOriginalLeftLinearLog D (g n) (a n)) :=
  native_sequential_adapted_factorization_cofinal D (nativeOriginalSubgroupLieFiltration D) L hL _
    (fun n => native_original_left_linear_log_weighted D (g n) (a n))

theorem native_original_subgroup_filtration_layer {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (j : ℕ) :
    (nativeOriginalSubgroupLieFiltration D).layer j =
      nativeLieLowerCentralModel (I := D.I) (G := D.G) (j-1) :=
  native_original_unstretched_lie_layer D j

end Hindman168
