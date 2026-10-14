import Hindman168.NativeLieAdjointDerivative

/-! The actual identity differential of a genuine smooth original group
homomorphism intertwines the genuine native adjoint actions. This is
proved by differentiating the actual original conjugation homomorphism
identity, without assuming bracket preservation. -/

namespace Hindman168
open Function
open scoped Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {G K : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [Group K] [TopologicalSpace K] [ChartedSpace H' K]
  [LieGroup I ∞ G] [LieGroup J ∞ K]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeSmoothHom_adjoint_intertwine (q : G →* K) (hq : ContMDiff I J ∞ q) (g : G) :
    let P : E →L[ℝ] F := mfderiv I J q 1
    P.comp (nativeLieAdjoint (I := I) g) =
      (nativeLieAdjoint (I := J) (q g)).comp P := by
  let c : G → G := fun x => g * x * g⁻¹
  let d : K → K := fun x => q g * x * (q g)⁻¹
  have hc : MDifferentiableAt I I c 1 :=
    (nativeLieConjugation_contMDiff (I := I) g).mdifferentiableAt (by norm_num)
  have hd : MDifferentiableAt J J d (q 1) :=
    (nativeLieConjugation_contMDiff (I := J) (q g)).mdifferentiableAt (by norm_num)
  have hq1 : MDifferentiableAt I J q 1 := hq.mdifferentiableAt (by norm_num)
  have hqc : MDifferentiableAt I J q (c 1) := hq.mdifferentiableAt (by norm_num)
  have he : q ∘ c = d ∘ q := by
    funext x
    change q (g * x * g⁻¹) = q g * q x * (q g)⁻¹
    simp only [map_mul, map_inv]
  have hleft := mfderiv_comp (1 : G) hqc hc
  have hright := mfderiv_comp (1 : G) hd hq1
  rw [he] at hleft
  have hc1 : c 1 = 1 := by dsimp [c]; simp
  rw [hc1] at hleft
  rw [q.map_one] at hright
  exact hleft.symm.trans hright

end Hindman168
