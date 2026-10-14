import Hindman168.NilUpperFaceGroup
import Mathlib.Tactic.Group

/-! The exact affine normalization in Proposition 7.5.  The automorphism is
constructed from the original ambient automorphism and the chosen basepoint
representative; its quotient action is then proved by group cancellation. -/
namespace Hindman168
variable {G : Type*} [Group G]

noncomputable def affineShearConjugatedAutomorphism (S : G ≃* G) (h c : G) : G ≃* G :=
  S.trans (MulAut.conj (c⁻¹ * h⁻¹ * S h))

 theorem affineShearConjugatedAutomorphism_apply (S : G ≃* G) (h c y : G) :
    affineShearConjugatedAutomorphism S h c y =
      (c⁻¹ * h⁻¹ * S h) * S y * (c⁻¹ * h⁻¹ * S h)⁻¹ := rfl

 theorem affineShear_coset_normalization (Γ : Subgroup G) (S : G ≃* G) (h c σ y : G)
    (hbase : (S (h * σ) : G ⧸ Γ) = (h * c * σ : G ⧸ Γ)) :
    (S (h * y * σ) : G ⧸ Γ) =
      (h * (c * affineShearConjugatedAutomorphism S h c y) * σ : G ⧸ Γ) := by
  apply QuotientGroup.eq.mpr
  have hb := QuotientGroup.eq.mp hbase
  convert hb using 1
  simp only [map_mul, affineShearConjugatedAutomorphism_apply]
  group

end Hindman168
