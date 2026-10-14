import Hindman168.AlignmentOriginalJointCubeOrbit
import Hindman168.AdaptedTaylorRecursion

/-! The actual original joint linear orbit has the ordered Taylor
coordinates needed to start section 7. Every coefficient belongs to its
actual original lower central layer, and the formula is exact at ALL
signed original integer inputs. No factorization/local Haar law is assumed. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

variable {ι : Type} [Fintype ι] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

theorem alignment_original_joint_taylor_representation
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) (ell : ℤ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    let P := nativeOriginalLeftLinearLog J (alignmentOriginalJointPointStep D n v hv T y g)
      (alignmentOriginalJointPointBase D n v hv F q₀ w T y p shift g a)
    alignmentOriginalJointPointOrbit D n v hv F q₀ w T y p shift g a ell =
      adaptedTaylorOrderedProduct J P (ell : ℝ) (s+1) := by
  dsimp only
  rw [← alignment_original_joint_point_orbit_log_source D n v hv F q₀ w T y p shift g a ell]
  exact adapted_taylor_full_ordered_representation _ _
    (alignment_original_joint_point_orbit_log_adapted D n v hv F q₀ w T y p shift g a) _

theorem alignment_original_joint_taylor_coefficient_layer
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) (j : ℕ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    let P := nativeOriginalLeftLinearLog J (alignmentOriginalJointPointStep D n v hv T y g)
      (alignmentOriginalJointPointBase D n v hv F q₀ w T y p shift g a)
    nativeLieExponential (E := J.E) (I := J.I) (G := J.G)
      (roughVectorMvEval (E := J.E) (adaptedTaylorResidual J P j) (fun _ => (j : ℝ))) ∈
      nilLowerCentralFiltration J.G j :=
  adapted_taylor_actual_coefficient_group_layer _ _
    (alignment_original_joint_point_orbit_log_adapted D n v hv F q₀ w T y p shift g a) j

end Hindman168
