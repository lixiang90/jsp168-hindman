import Hindman168.NativeSmoothHomLieBracket
import Mathlib.Algebra.Lie.Prod

/-! The native Lie algebra of a product of the original Lie groups is
the product of their original native Lie algebras. The bracket comparison
uses genuine smooth projection homomorphisms and their differentials. -/

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

theorem nativeProductLie_bracket_fst (v w : GroupLieAlgebra (I.prod J) (G × K)) :
    (⁅v, w⁆ : GroupLieAlgebra (I.prod J) (G × K)).1 =
      (⁅(show GroupLieAlgebra I G from v.1),
        (show GroupLieAlgebra I G from w.1)⁆ : GroupLieAlgebra I G) := by
  have h := nativeSmoothHom_bracket (I := I.prod J) (J := I)
    (MonoidHom.fst G K) contMDiff_fst v w
  change (mfderiv (I.prod J) I (@Prod.fst G K) 1) ⁅v, w⁆ =
    ⁅(show GroupLieAlgebra I G from (mfderiv (I.prod J) I (@Prod.fst G K) 1) v),
      (show GroupLieAlgebra I G from (mfderiv (I.prod J) I (@Prod.fst G K) 1) w)⁆ at h
  rw [mfderiv_fst] at h
  exact h

theorem nativeProductLie_bracket_snd (v w : GroupLieAlgebra (I.prod J) (G × K)) :
    (⁅v, w⁆ : GroupLieAlgebra (I.prod J) (G × K)).2 =
      (⁅(show GroupLieAlgebra J K from v.2),
        (show GroupLieAlgebra J K from w.2)⁆ : GroupLieAlgebra J K) := by
  have h := nativeSmoothHom_bracket (I := I.prod J) (J := J)
    (MonoidHom.snd G K) contMDiff_snd v w
  change (mfderiv (I.prod J) J (@Prod.snd G K) 1) ⁅v, w⁆ =
    ⁅(show GroupLieAlgebra J K from (mfderiv (I.prod J) J (@Prod.snd G K) 1) v),
      (show GroupLieAlgebra J K from (mfderiv (I.prod J) J (@Prod.snd G K) 1) w)⁆ at h
  rw [mfderiv_snd] at h
  exact h

noncomputable def nativeProductLieEquiv :
    GroupLieAlgebra (I.prod J) (G × K) ≃ₗ⁅ℝ⁆
      (GroupLieAlgebra I G × GroupLieAlgebra J K) where
  toFun v := (v.1, v.2)
  invFun v := (v.1, v.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := by
    intro v w
    exact Prod.ext (nativeProductLie_bracket_fst v w) (nativeProductLie_bracket_snd v w)

end Hindman168
