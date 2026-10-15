import Hindman168.OriginalSameStepLinearizationTime
import Hindman168.OriginalSameStepLinearizationReal
import Hindman168.OriginalSameStepLinearizationOrbit

/-!
# Real inputs and rational time in the original-step BCH extension

The input polynomial may have arbitrary real coefficients.  Only the time
translation is rational.  Finite Hadamard commutes with scalar extension,
so the rational conjugation identity holds on the entire real fibre.
-/

namespace Hindman168.OriginalSameStepLinearization

open OAI.Erdos3
open OriginalSameStepLinearizationConjugation
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (hs : 1 ≤ s) (d : ℕ)

abbrev RealAmbientGroup := (filtration F hs d).realification.Group

/-- The real fibre embeds in the realification of the original-step Lie extension. -/
noncomputable def realAmbientFiberInclusion :
    RealFiberGroup F d →* RealAmbientGroup F hs d :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (fiberFiltration F d).lowerCentralSeries_eq_bot)
    (hM := (filtration F hs d).lowerCentralSeries_eq_bot)
    (LieAlgebra.SemiDirectSum.inl (action F d))

/-- The time element stays rational before inclusion into the real group. -/
noncomputable def realTimeInclusion :
    Multiplicative (TimeTorus.Algebra d) →* RealAmbientGroup F hs d :=
  (NilpotentLieBCHGroup.realificationHom
    (hnil := (filtration F hs d).lowerCentralSeries_eq_bot)).comp (timeInclusion F hs d)

/-- Conjugation holds for every real fibre input, not merely rational points. -/
theorem real_time_conjugation (h : TimeTorus.Algebra d) (p : RealFiberGroup F d) :
    realTimeInclusion F hs d (Multiplicative.ofAdd h) * realAmbientFiberInclusion F hs d p *
      (realTimeInclusion F hs d (Multiplicative.ofAdd h))⁻¹ =
      realAmbientFiberInclusion F hs d (realFiberTranslation F d h p) := by
  apply NilpotentLieBCHGroup.ext
  rw [conjugation_coord]
  change adjointSum s (1 ⊗ₜ[ℚ] (LieAlgebra.SemiDirectSum.inr (action F d) h))
      ((LieAlgebra.SemiDirectSum.inl (action F d)).toLinearMap.baseChange ℝ p.coord) =
    (LieAlgebra.SemiDirectSum.inl (action F d)).toLinearMap.baseChange ℝ
      ((fiberTranslation F d h).toLinearMap.baseChange ℝ p.coord)
  exact adjointSum_baseChange s (LieAlgebra.SemiDirectSum.inr (action F d) h)
    (LieAlgebra.SemiDirectSum.inl (action F d)).toLinearMap
    (fiberTranslation F d h).toLinearMap (time_adjointSum_fiber F d h) p.coord

/-- The real fibre translation is invertible. -/
noncomputable def realFiberTranslationGroup (h : TimeTorus.Algebra d) :
    MulAut (RealFiberGroup F d) where
  toFun := realFiberTranslation F d h
  invFun := realFiberTranslation F d (-h)
  left_inv p := by
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom (fiberTranslation F d (-h))
      (realificationLieHom (fiberTranslation F d h) p.coord) = p.coord
    induction p.coord using TensorProduct.induction_on with
    | zero => simp
    | tmul r p =>
      simp only [realificationLieHom_tmul]
      exact congrArg (fun q => r ⊗ₜ[ℚ] q) ((fiberTranslationEquiv F d h).left_inv p)
    | add p q hp hq => simp only [map_add, hp, hq]
  right_inv p := by
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom (fiberTranslation F d h)
      (realificationLieHom (fiberTranslation F d (-h)) p.coord) = p.coord
    induction p.coord using TensorProduct.induction_on with
    | zero => simp
    | tmul r p =>
      simp only [realificationLieHom_tmul]
      exact congrArg (fun q => r ⊗ₜ[ℚ] q) ((fiberTranslationEquiv F d h).right_inv p)
    | add p q hp hq => simp only [map_add, hp, hq]
  map_mul' := map_mul (realFiberTranslation F d h)

/-- Rational translations act on the full real BCH fibre group. -/
noncomputable def realFiberTranslationAction :
    Multiplicative (TimeTorus.Algebra d) →* MulAut (RealFiberGroup F d) where
  toFun h := realFiberTranslationGroup F d h.toAdd
  map_one' := by
    apply MulEquiv.ext
    intro p
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom (fiberTranslation F d 0) p.coord = p.coord
    induction p.coord using TensorProduct.induction_on with
    | zero => simp
    | tmul r p =>
      simp only [realificationLieHom_tmul]
      congr 1
      apply Subtype.ext
      exact adaptedTranslation_zero F p.val
    | add p q hp hq => simp only [map_add, hp, hq]
  map_mul' h k := by
    apply MulEquiv.ext
    intro p
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom (fiberTranslation F d (h.toAdd + k.toAdd)) p.coord =
      realificationLieHom (fiberTranslation F d h.toAdd)
        (realificationLieHom (fiberTranslation F d k.toAdd) p.coord)
    induction p.coord using TensorProduct.induction_on with
    | zero => simp
    | tmul r p =>
      simp only [realificationLieHom_tmul]
      congr 1
      apply Subtype.ext
      exact (adaptedTranslation_comp F h.toAdd k.toAdd p.val).symm
    | add p q hp hq => simp only [map_add, hp, hq]

/-- The real-fibre, rational-time semidirect product maps to the same-step real BCH group. -/
noncomputable def realSemidirectLift :
    (RealFiberGroup F d ⋊[realFiberTranslationAction F d]
      Multiplicative (TimeTorus.Algebra d)) →* RealAmbientGroup F hs d :=
  splitLift (realFiberTranslationAction F d) (realAmbientFiberInclusion F hs d)
    (realTimeInclusion F hs d) (fun h p => (real_time_conjugation F hs d h.toAdd p).symm)

@[simp] theorem realSemidirectLift_apply
    (x : RealFiberGroup F d ⋊[realFiberTranslationAction F d]
      Multiplicative (TimeTorus.Algebra d)) :
    realSemidirectLift F hs d x =
      realAmbientFiberInclusion F hs d x.left * realTimeInclusion F hs d x.right := rfl

/-- Integer multiples of a fixed rational time vector. -/
def integerDirection (h : TimeTorus.Algebra d) :
    Multiplicative ℤ →* Multiplicative (TimeTorus.Algebra d) where
  toFun n := Multiplicative.ofAdd (n.toAdd • h)
  map_one' := by simp
  map_mul' n m := by simp [add_zsmul]

/-- Restriction to the integer time direction used by the orbit realization. -/
noncomputable def realIntegerTranslationAction (h : TimeTorus.Algebra d) :
    Multiplicative ℤ →* MulAut (RealFiberGroup F d) :=
  (realFiberTranslationAction F d).comp (integerDirection d h)

/-- This is the required homomorphism for arbitrary real fibre elements and integer time. -/
noncomputable def realIntegerSemidirectLift (h : TimeTorus.Algebra d) :
    (RealFiberGroup F d ⋊[realIntegerTranslationAction F d h] Multiplicative ℤ) →*
      RealAmbientGroup F hs d :=
  splitLift (realIntegerTranslationAction F d h) (realAmbientFiberInclusion F hs d)
    ((realTimeInclusion F hs d).comp (integerDirection d h))
    (fun n p => (real_time_conjugation F hs d (n.toAdd • h) p).symm)

@[simp] theorem realIntegerSemidirectLift_apply (h : TimeTorus.Algebra d)
    (x : RealFiberGroup F d ⋊[realIntegerTranslationAction F d h] Multiplicative ℤ) :
    realIntegerSemidirectLift F hs d h x = realAmbientFiberInclusion F hs d x.left *
      realTimeInclusion F hs d (Multiplicative.ofAdd (x.right.toAdd • h)) := rfl

/-- Rational evaluation commutes with translation on all real fibre elements. -/
theorem realFiberEvaluation_translation (x h : Fin d → ℚ) (p : RealFiberGroup F d) :
    realFiberEvaluation F d x (realFiberTranslation F d h p) =
      realFiberEvaluation F d (x + h) p := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (fiberEvaluationLie F d x)
    (realificationLieHom (fiberTranslation F d h) p.coord) =
      realificationLieHom (fiberEvaluationLie F d (x + h)) p.coord
  induction p.coord using TensorProduct.induction_on with
  | zero => simp
  | tmul r p =>
    simp only [realificationLieHom_tmul]
    congr 1
    exact VectorPolynomial.eval_translate h x p.val.val
  | add p q hp hq => simp only [map_add, hp, hq]

/-- Evaluation along integer multiples of the chosen rational direction. -/
noncomputable def realFiberSequence (h : TimeTorus.Algebra d) :
    RealFiberGroup F d →* (ℤ → F.realification.Group) where
  toFun p k := realFiberEvaluation F d (k • h) p
  map_one' := by funext k; exact map_one _
  map_mul' p q := by funext k; exact map_mul _ p q

/-- The exact equivariance needed by the all-integer orbit theorem. -/
theorem realFiberSequence_equivariant (h : TimeTorus.Algebra d)
    (n : Multiplicative ℤ) (p : RealFiberGroup F d) (k : ℤ) :
    realFiberSequence F d h (realIntegerTranslationAction F d h n p) k =
      realFiberSequence F d h p (k + n.toAdd) := by
  change realFiberEvaluation F d (k • h) (realFiberTranslation F d (n.toAdd • h) p) =
    realFiberEvaluation F d ((k + n.toAdd) • h) p
  rw [realFiberEvaluation_translation]
  apply congrArg (fun x : Fin d → ℚ => realFiberEvaluation F d x p)
  exact (add_zsmul h k n.toAdd).symm

/-- The integer-orbit theorem applies to the concrete real polynomial fibre action. -/
theorem realInteger_based_orbit (h : TimeTorus.Algebra d)
    (g : ℤ → F.realification.Group) (a c : RealFiberGroup F d)
    (ha : realFiberSequence F d h a =
      OriginalSameStepLinearizationOrbit.rightDifference
        (OriginalSameStepLinearizationOrbit.normalize g))
    (hc : realFiberSequence F d h c = fun _ => g 0) (n : ℤ) :
    realFiberEvaluation F d 0
      ((((⟨a, Multiplicative.ofAdd 1⟩ :
        RealFiberGroup F d ⋊[realIntegerTranslationAction F d h] Multiplicative ℤ) ^ n) *
        (⟨c, 1⟩ : RealFiberGroup F d ⋊[realIntegerTranslationAction F d h]
          Multiplicative ℤ)).left) = g n := by
  have he := OriginalSameStepLinearizationOrbit.abstract_based_orbit
    (realIntegerTranslationAction F d h) (realFiberSequence F d h)
    (realFiberSequence_equivariant F d h) g a c ha hc n
  change realFiberEvaluation F d ((0 : ℤ) • h) _ = g n at he
  rw [zero_zsmul] at he
  exact he

end Hindman168.OriginalSameStepLinearization
