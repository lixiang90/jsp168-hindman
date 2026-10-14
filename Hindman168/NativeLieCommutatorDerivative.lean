import Hindman168.NativeLieAdjointInfinitesimal
import Hindman168.NilLowerCentralCommutator

/-! Differentiate the actual original group commutator at the identity.
The derivative is obtained from the actual multiplication chain rule and
the genuine identity commutator(g,x)*x = conjugation(g,x). -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

attribute [local instance] lieGroup_smooth_min_three

 def nativeGroupCommutatorMap (g x : G) : G := g * x * g⁻¹ * x⁻¹

omit [TopologicalSpace G] in
 theorem nativeGroupCommutatorMap_one (g : G) : nativeGroupCommutatorMap g 1 = 1 := by
  simp [nativeGroupCommutatorMap]

 theorem nativeGroupCommutatorMap_contMDiff (g : G) :
    ContMDiff I I ∞ (nativeGroupCommutatorMap g) := by
  exact (nativeLieConjugation_contMDiff (I := I) g).mul (contMDiff_inv I ∞)

 theorem nativeLieMultiplication_mfderiv_identity (u v : E) :
    mfderiv (I.prod I) I (fun p : G × G => p.1 * p.2) (1, 1) (u, v) = u + v := by
  rw [mfderiv_prod_eq_add_apply ((contMDiff_mul I ∞).mdifferentiableAt (by norm_num))]
  have hr : (fun x : G => x * 1) = id := by funext x; exact mul_one x
  have hl : (fun x : G => (1 : G) * x) = id := by funext x; exact one_mul x
  erw [hr, hl, mfderiv_id]
  rfl

 theorem nativeGroupCommutatorMap_mfderiv (g : G) :
    mfderiv I I (nativeGroupCommutatorMap g) (1 : G) =
      nativeLieAdjoint (I := I) g - ContinuousLinearMap.id ℝ E := by
  let c := nativeGroupCommutatorMap g
  let C : E →L[ℝ] E := mfderiv I I c (1 : G)
  have hc : MDifferentiableAt I I c (1 : G) :=
    (nativeGroupCommutatorMap_contMDiff (I := I) g).mdifferentiableAt (by norm_num)
  have hi : MDifferentiableAt I I (id : G → G) (1 : G) := mdifferentiableAt_id
  have hp : (c (1 : G), (1 : G)) = (1, 1) := by
    change (nativeGroupCommutatorMap g 1, (1 : G)) = (1, 1)
    rw [nativeGroupCommutatorMap_one]
  have he : (fun p : G × G => p.1 * p.2) ∘ (fun x : G => (c x, id x)) =
      (fun x : G => g * x * g⁻¹) := by
    funext x
    simp only [comp_apply, id_eq, c, nativeGroupCommutatorMap]
    group
  change C = nativeLieAdjoint (I := I) g - ContinuousLinearMap.id ℝ E
  apply ContinuousLinearMap.ext
  intro v
  have hd := mfderiv_comp_apply_of_eq (I := I) (I' := I.prod I) (I'' := I)
    (1 : G) ((contMDiff_mul I ∞).mdifferentiableAt (by norm_num)) (hc.prodMk hi) hp v
  rw [he] at hd
  erw [mfderiv_prodMk hc hi, mfderiv_id] at hd
  change nativeLieAdjoint (I := I) g v =
    mfderiv (I.prod I) I (fun p : G × G => p.1 * p.2) (1, 1)
      (mfderiv I I c (1 : G) v, v) at hd
  rw [nativeLieMultiplication_mfderiv_identity] at hd
  have he' : nativeLieAdjoint (I := I) g v = C v + v := hd
  change C v = nativeLieAdjoint (I := I) g v - v
  exact eq_sub_of_add_eq he'.symm

end Hindman168
