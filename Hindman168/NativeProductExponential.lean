import Hindman168.NativeProductLieAlgebra
import Hindman168.LieExponentialHomomorphism

/-! The constructed native exponential of the product is precisely the
pair of the original constructed exponentials. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {G K : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [Group K] [TopologicalSpace K] [ChartedSpace H' K]
  [LieGroup I ∞ G] [LieGroup J ∞ K] [BoundarylessManifold I G]
  [BoundarylessManifold J K] [T2Space G] [T2Space K]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeProductExponential_fst (v : GroupLieAlgebra (I.prod J) (G × K)) :
    (nativeLieExponential (I := I.prod J) (G := G × K) v).1 =
      nativeLieExponential (I := I) (G := G) v.1 := by
  have h := nativeLieExponential_map (I := I.prod J) (J := I)
    (MonoidHom.fst G K) mdifferentiable_fst v
  change (nativeLieExponential (I := I.prod J) (G := G × K) v).1 =
    nativeLieExponential (I := I) (G := G)
      ((mfderiv (I.prod J) I (@Prod.fst G K) 1) v) at h
  rw [mfderiv_fst] at h
  exact h

theorem nativeProductExponential_snd (v : GroupLieAlgebra (I.prod J) (G × K)) :
    (nativeLieExponential (I := I.prod J) (G := G × K) v).2 =
      nativeLieExponential (I := J) (G := K) v.2 := by
  have h := nativeLieExponential_map (I := I.prod J) (J := J)
    (MonoidHom.snd G K) mdifferentiable_snd v
  change (nativeLieExponential (I := I.prod J) (G := G × K) v).2 =
    nativeLieExponential (I := J) (G := K)
      ((mfderiv (I.prod J) J (@Prod.snd G K) 1) v) at h
  rw [mfderiv_snd] at h
  exact h

theorem nativeProductExponential_eq (v : GroupLieAlgebra (I.prod J) (G × K)) :
    nativeLieExponential (I := I.prod J) (G := G × K) v =
      (nativeLieExponential (I := I) (G := G) v.1,
        nativeLieExponential (I := J) (G := K) v.2) :=
  Prod.ext (nativeProductExponential_fst v) (nativeProductExponential_snd v)

end Hindman168
