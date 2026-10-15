import Hindman168.OriginalSameStepLinearizationSplit
import Hindman168.OriginalSameStepLinearizationTranslation
import Hindman168.OriginalSameStepLinearizationConjugation
import Hindman168.OriginalSameStepLinearizationFiberTaylor

/-! The split-extension group isomorphism used for the BCH time direction. -/

namespace Hindman168.OriginalSameStepLinearization



section TimeDirection

open OAI.Erdos3
open OriginalSameStepLinearizationConjugation

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (hs : 1 ≤ s) (d : ℕ)

/-- Inclusion of the polynomial fibre into the BCH group of the same-step Lie extension. -/
noncomputable def fiberInclusion : FiberGroup F d →* Group F hs d :=
  NilpotentLieBCHGroup.map (LieAlgebra.SemiDirectSum.inl (action F d))

@[simp] theorem fiberInclusion_coord (p : FiberGroup F d) :
    (fiberInclusion F hs d p).coord = ⟨p.coord, 0⟩ := rfl

theorem fiberInclusion_injective : Function.Injective (fiberInclusion F hs d) := by
  intro p q hpq
  apply NilpotentLieBCHGroup.ext
  exact congrArg (fun x : Group F hs d => x.coord.left) hpq

/-- The pure time direction, with its additive coordinates regarded multiplicatively. -/
noncomputable def timeInclusion : Multiplicative (TimeTorus.Algebra d) →* Group F hs d where
  toFun h := ⟨LieAlgebra.SemiDirectSum.inr (action F d) h.toAdd⟩
  map_one' := NilpotentLieBCHGroup.ext (map_zero _)
  map_mul' h k := by
    apply NilpotentLieBCHGroup.ext
    change LieAlgebra.SemiDirectSum.inr (action F d) (h.toAdd + k.toAdd) =
      lieBCH s (LieAlgebra.SemiDirectSum.inr (action F d) h.toAdd)
        (LieAlgebra.SemiDirectSum.inr (action F d) k.toAdd)
    rw [← map_lieBCH, lieBCH_eq_add_of_lie_eq_zero_pos hs (TimeTorus.lie_eq_zero _ _)]

@[simp] theorem timeInclusion_coord (h : Multiplicative (TimeTorus.Algebra d)) :
    (timeInclusion F hs d h).coord = ⟨0, h.toAdd⟩ := rfl

/-- Projection onto the time coordinate is a genuine group homomorphism. -/
noncomputable def timeProjection : Group F hs d →* Multiplicative (TimeTorus.Algebra d) where
  toFun x := Multiplicative.ofAdd x.coord.right
  map_one' := rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    change (lieBCH s x.coord y.coord).right = x.coord.right + y.coord.right
    have h := map_lieBCH (LieAlgebra.SemiDirectSum.projr (action F d)) s x.coord y.coord
    rw [lieBCH_eq_add_of_lie_eq_zero_pos hs (TimeTorus.lie_eq_zero _ _)] at h
    exact h

@[simp] theorem timeProjection_fiberInclusion (p : FiberGroup F d) :
    timeProjection F hs d (fiberInclusion F hs d p) = 1 := rfl

@[simp] theorem timeProjection_timeInclusion (h : Multiplicative (TimeTorus.Algebra d)) :
    timeProjection F hs d (timeInclusion F hs d h) = h := rfl

/-- The fibre is exactly the kernel of the time projection. -/
theorem timeProjection_kernel (x : Group F hs d) (hx : timeProjection F hs d x = 1) :
    ∃ p : FiberGroup F d, fiberInclusion F hs d p = x := by
  refine ⟨⟨x.coord.left⟩, ?_⟩
  apply NilpotentLieBCHGroup.ext
  apply LieAlgebra.SemiDirectSum.ext
  · rfl
  · exact (congrArg Multiplicative.toAdd hx).symm

/-- Translation is an automorphism of the BCH fibre group. -/
noncomputable def fiberTranslationGroup (h : TimeTorus.Algebra d) : MulAut (FiberGroup F d) where
  toFun p := ⟨fiberTranslation F d h p.coord⟩
  invFun p := ⟨fiberTranslation F d (-h) p.coord⟩
  left_inv p := NilpotentLieBCHGroup.ext ((fiberTranslationEquiv F d h).left_inv p.coord)
  right_inv p := NilpotentLieBCHGroup.ext ((fiberTranslationEquiv F d h).right_inv p.coord)
  map_mul' p q := NilpotentLieBCHGroup.ext (map_lieBCH (fiberTranslation F d h) s p.coord q.coord)

@[simp] theorem fiberTranslationGroup_coord (h : TimeTorus.Algebra d) (p : FiberGroup F d) :
    (fiberTranslationGroup F d h p).coord = fiberTranslation F d h p.coord := rfl

/-- The additive translation directions act on the fibre BCH group. -/
noncomputable def fiberTranslationAction :
    Multiplicative (TimeTorus.Algebra d) →* MulAut (FiberGroup F d) where
  toFun h := fiberTranslationGroup F d h.toAdd
  map_one' := by
    apply MulEquiv.ext
    intro p
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    exact adaptedTranslation_zero F p.coord.val
  map_mul' h k := by
    apply MulEquiv.ext
    intro p
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    exact (adaptedTranslation_comp F h.toAdd k.toAdd p.coord.val).symm

/-- The bracket of pure time with a fibre element is its directional derivative. -/
theorem time_lie_fiber (h : TimeTorus.Algebra d) (p : Fiber F d) :
    ⁅LieAlgebra.SemiDirectSum.inr (action F d) h,
      LieAlgebra.SemiDirectSum.inl (action F d) p⁆ =
      LieAlgebra.SemiDirectSum.inl (action F d) (derivative F d h p) := by
  change ⁅LieAlgebra.SemiDirectSum.inr (action F d) h,
    LieAlgebra.SemiDirectSum.inl (action F d) p⁆ =
      LieAlgebra.SemiDirectSum.inl (action F d) ((action F d) h p)
  simp

/-- Iterated adjoints in the time direction are the corresponding iterated derivatives. -/
theorem time_ad_pow_fiber (h : TimeTorus.Algebra d) (p : Fiber F d) (n : ℕ) :
    (LieAlgebra.ad ℚ (Algebra F d) (LieAlgebra.SemiDirectSum.inr (action F d) h) ^ n)
      (LieAlgebra.SemiDirectSum.inl (action F d) p) =
      LieAlgebra.SemiDirectSum.inl (action F d)
        ((((derivative F d h).toLinearMap : Module.End ℚ (Fiber F d)) ^ n) p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    rw [LieAlgebra.ad_apply, time_lie_fiber, pow_succ', Module.End.mul_apply]
    rfl

/-- Finite Hadamard for the time/fibre pair, before rewriting the finite Taylor sum. -/
theorem time_conjugation_coord_sum (h : TimeTorus.Algebra d) (p : FiberGroup F d) :
    (timeInclusion F hs d (Multiplicative.ofAdd h) * fiberInclusion F hs d p *
      (timeInclusion F hs d (Multiplicative.ofAdd h))⁻¹).coord =
      LieAlgebra.SemiDirectSum.inl (action F d)
        (∑ n ∈ Finset.range s, ((n.factorial : ℚ)⁻¹) •
          (((derivative F d h).toLinearMap : Module.End ℚ (Fiber F d)) ^ n) p.coord) := by
  rw [conjugation_coord]
  simp only [timeInclusion_coord, fiberInclusion_coord, adjointSum]
  change (∑ n ∈ Finset.range s, ((n.factorial : ℚ)⁻¹) •
      (LieAlgebra.ad ℚ (Algebra F d) (LieAlgebra.SemiDirectSum.inr (action F d) h) ^ n)
        (LieAlgebra.SemiDirectSum.inl (action F d) p.coord)) = _
  simp only [time_ad_pow_fiber, map_sum, map_smul]

/-- In the time direction, finite Hadamard is exactly polynomial translation. -/
theorem time_adjointSum_fiber (h : TimeTorus.Algebra d) (p : Fiber F d) :
    adjointSum s (LieAlgebra.SemiDirectSum.inr (action F d) h)
      (LieAlgebra.SemiDirectSum.inl (action F d) p) =
      LieAlgebra.SemiDirectSum.inl (action F d) (fiberTranslation F d h p) := by
  rw [fiberTranslation_eq_sum]
  simp only [adjointSum, time_ad_pow_fiber, map_sum, map_smul]

/-- Exact conjugation by the BCH time element gives the translation action. -/
theorem time_conjugation (h : TimeTorus.Algebra d) (p : FiberGroup F d) :
    timeInclusion F hs d (Multiplicative.ofAdd h) * fiberInclusion F hs d p *
      (timeInclusion F hs d (Multiplicative.ofAdd h))⁻¹ =
      fiberInclusion F hs d (fiberTranslationGroup F d h p) := by
  apply NilpotentLieBCHGroup.ext
  rw [conjugation_coord]
  exact time_adjointSum_fiber F d h p.coord

/-- The shift semidirect product maps into the original-step BCH group. -/
noncomputable def rationalSemidirectLift :
    (FiberGroup F d ⋊[fiberTranslationAction F d] Multiplicative (TimeTorus.Algebra d)) →*
      Group F hs d :=
  splitLift (fiberTranslationAction F d) (fiberInclusion F hs d) (timeInclusion F hs d)
    (fun h p => (time_conjugation F hs d h.toAdd p).symm)

/-- In fact the rational BCH extension is exactly the translation semidirect product. -/
noncomputable def rationalSemidirectEquiv :
    (FiberGroup F d ⋊[fiberTranslationAction F d] Multiplicative (TimeTorus.Algebra d)) ≃*
      Group F hs d :=
  splitEquiv (fiberTranslationAction F d) (fiberInclusion F hs d) (timeInclusion F hs d)
    (timeProjection F hs d) (fun h p => (time_conjugation F hs d h.toAdd p).symm)
    (fiberInclusion_injective F hs d) (timeProjection_fiberInclusion F hs d)
    (timeProjection_timeInclusion F hs d) (timeProjection_kernel F hs d)

end TimeDirection

end Hindman168.OriginalSameStepLinearization
