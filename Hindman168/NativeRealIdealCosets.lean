import Hindman168.NativeLieRationalIdealCosets
import Hindman168.NativeLieIdealSubgroup

/-! Exact original coset criterion for any REAL native Lie ideal.
Restricting the real model to Q lets the proved native BCH ideal theorem
apply to arbitrary real vectors; no rationality premise is added. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeLieGlobalLogarithm_real_ideal_product
    (J : LieIdeal ℝ (GroupLieAlgebra I G)) (g : G) {n : E}
    (hn : n ∈ nativeLieSubalgebraModel J.toLieSubalgebra) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      (g * nativeLieExponential (I := I) (G := G) n) -
        nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈
      nativeLieSubalgebraModel J.toLieSubalgebra := by
  let N := (nativeLieSubalgebraModel (E := E) J.toLieSubalgebra).restrictScalars ℚ
  have hI : ∀ v ∈ (⊤ : Submodule ℚ E), ∀ w ∈ N,
      nativeLieAdjointDifferential (I := I) (G := G) v w ∈ N := by
    intro v _ w hw
    have hm := nativeLieAdjointGenerator_mem_ideal J v hw
    rwa [nativeLieAdjointGenerator_eq_differential] at hm
  let u := nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g
  have hp := nativeLieGlobalLogarithm_product_pair_ideal (I := I) (G := G)
    ⊤ N le_top hI Submodule.mem_top Submodule.mem_top
      (hI u Submodule.mem_top n hn)
  rw [nativeLieExponential_globalLogarithm] at hp
  have hm := N.add_mem hp hn
  change nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
    (g * nativeLieExponential (I := I) (G := G) n) - u ∈ N
  have he : nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      (g * nativeLieExponential (I := I) (G := G) n) - u =
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      (g * nativeLieExponential (I := I) (G := G) n) - (u+n) + n := by abel
  rw [he]
  exact hm

theorem native_real_ideal_coset_log_iff
    (J : LieIdeal ℝ (GroupLieAlgebra I G)) (g h : G) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g -
      nativeLieGlobalLogarithm (E := E) (I := I) (G := G) h ∈
        nativeLieSubalgebraModel J.toLieSubalgebra ↔
      h⁻¹*g ∈ nativeLieSubalgebraSubgroup (E := E) J.toLieSubalgebra := by
  let N := (nativeLieSubalgebraModel (E := E) J.toLieSubalgebra).restrictScalars ℚ
  have hI : ∀ v ∈ (⊤ : Submodule ℚ E), ∀ w ∈ N,
      nativeLieAdjointDifferential (I := I) (G := G) v w ∈ N := by
    intro v _ w hw
    have hm := nativeLieAdjointGenerator_mem_ideal J v hw
    rwa [nativeLieAdjointGenerator_eq_differential] at hm
  constructor
  · intro hgh
    have hl := nativeLieGlobalLogarithm_ideal_difference (I := I) (G := G)
      ⊤ N le_top hI Submodule.mem_top Submodule.mem_top hgh
    rw [nativeLieExponential_globalLogarithm,nativeLieExponential_globalLogarithm] at hl
    have hm := (nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff (E := E)
      J.toLieSubalgebra (g*h⁻¹)).mpr hl
    exact (nativeLieIdealSubgroup_normal J).mem_comm_iff.mp hm
  · intro hgh
    have hn := (nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff (E := E)
      J.toLieSubalgebra (h⁻¹*g)).mp hgh
    have hp := nativeLieGlobalLogarithm_real_ideal_product (I := I) J h hn
    rwa [nativeLieExponential_globalLogarithm,mul_inv_cancel_left] at hp

end Hindman168
