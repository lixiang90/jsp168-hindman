import Hindman168.RoughConjugateLatticeTopology

/-! TRUE right translation between DIFFERENT actual nonnormal quotients.
It is equivariant for the original LEFT group action; no arbitrary right
action on the original quotient is supplied. -/
namespace Hindman168
variable {G : Type*} [Group G]

noncomputable def roughConjugateRightCosetMap (Γ : Subgroup G) (g : G) :
    G ⧸ roughConjugateSubgroup Γ g → G ⧸ Γ :=
  Quotient.lift (fun x : G => (QuotientGroup.mk (x*g) : G ⧸ Γ))
    (fun x y h => by
      apply QuotientGroup.eq.mpr
      have hh := (roughConjugateSubgroup_mem_iff Γ g (x⁻¹*y)).mp (QuotientGroup.leftRel_apply.mp h)
      convert hh using 1
      group)

noncomputable def roughConjugateRightCosetInverse (Γ : Subgroup G) (g : G) :
    G ⧸ Γ → G ⧸ roughConjugateSubgroup Γ g :=
  Quotient.lift (fun x : G => (QuotientGroup.mk (x*g⁻¹) : G ⧸ roughConjugateSubgroup Γ g))
    (fun x y h => by
      apply QuotientGroup.eq.mpr
      have hh := (roughConjugateSubgroup_mem Γ g (x⁻¹*y)).mpr (QuotientGroup.leftRel_apply.mp h)
      convert hh using 1
      group)

theorem rough_conjugate_right_coset_map_mk (Γ : Subgroup G) (g x : G) :
    roughConjugateRightCosetMap Γ g (x : G ⧸ roughConjugateSubgroup Γ g)=(x*g : G ⧸ Γ) := rfl

theorem rough_conjugate_right_coset_inverse_mk (Γ : Subgroup G) (g x : G) :
    roughConjugateRightCosetInverse Γ g (x : G ⧸ Γ)=(x*g⁻¹ : G ⧸ roughConjugateSubgroup Γ g) := rfl

theorem rough_conjugate_right_coset_left_inverse (Γ : Subgroup G) (g : G) :
    Function.LeftInverse (roughConjugateRightCosetInverse Γ g) (roughConjugateRightCosetMap Γ g) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
    change ((x*g)*g⁻¹ : G ⧸ roughConjugateSubgroup Γ g)=(x : G ⧸ roughConjugateSubgroup Γ g)
    rw [mul_inv_cancel_right]

theorem rough_conjugate_right_coset_right_inverse (Γ : Subgroup G) (g : G) :
    Function.RightInverse (roughConjugateRightCosetInverse Γ g) (roughConjugateRightCosetMap Γ g) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
    change ((x*g⁻¹)*g : G ⧸ Γ)=(x : G ⧸ Γ)
    rw [inv_mul_cancel_right]

noncomputable def roughConjugateRightCosetEquiv (Γ : Subgroup G) (g : G) :
    G ⧸ roughConjugateSubgroup Γ g ≃ G ⧸ Γ where
  toFun := roughConjugateRightCosetMap Γ g
  invFun := roughConjugateRightCosetInverse Γ g
  left_inv := rough_conjugate_right_coset_left_inverse Γ g
  right_inv := rough_conjugate_right_coset_right_inverse Γ g

theorem rough_conjugate_right_coset_equivariant (Γ : Subgroup G) (g h : G)
    (q : G ⧸ roughConjugateSubgroup Γ g) :
    roughConjugateRightCosetMap Γ g (h • q)=h • roughConjugateRightCosetMap Γ g q := by
  induction q using Quotient.inductionOn with
  | _ x =>
    change ((h*x)*g : G ⧸ Γ)=(h*(x*g) : G ⧸ Γ)
    rw [mul_assoc]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem rough_conjugate_right_coset_map_continuous (Γ : Subgroup G) (g : G) :
    Continuous (roughConjugateRightCosetMap Γ g) := by
  apply continuous_quot_lift
  exact QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)

theorem rough_conjugate_right_coset_inverse_continuous (Γ : Subgroup G) (g : G) :
    Continuous (roughConjugateRightCosetInverse Γ g) := by
  apply continuous_quot_lift
  exact QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)

noncomputable def roughConjugateRightCosetHomeomorph (Γ : Subgroup G) (g : G) :
    G ⧸ roughConjugateSubgroup Γ g ≃ₜ G ⧸ Γ where
  toEquiv := roughConjugateRightCosetEquiv Γ g
  continuous_toFun := rough_conjugate_right_coset_map_continuous Γ g
  continuous_invFun := rough_conjugate_right_coset_inverse_continuous Γ g

end Hindman168
