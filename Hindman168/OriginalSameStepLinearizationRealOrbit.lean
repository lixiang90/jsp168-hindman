import Hindman168.OriginalSameStepLinearizationRealTime

/-! Exact all-integer polynomial-orbit recovery, with the initial value in
an actual basepoint and evaluation at zero as the fixed observer. -/

namespace Hindman168.OriginalSameStepLinearization

open OAI.Erdos3
open OriginalSameStepLinearizationOrbit

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (d : ℕ)

noncomputable def realPolynomialSequence (h : TimeTorus.Algebra d)
    (p : RealAdaptedGroup F (fun _ : Fin d => 1)) : ℤ → F.realification.Group :=
  fun k => realAdaptedEvaluation F (k • h) p

noncomputable def normalizedRealPolynomial
    (p : RealAdaptedGroup F (fun _ : Fin d => 1)) :
    RealAdaptedGroup F (fun _ : Fin d => 1) :=
  p * (realFiberInclusion F d
    (realFiberConstant F d (realAdaptedEvaluation F 0 p)))⁻¹

theorem realPolynomialSequence_normalized (h : TimeTorus.Algebra d)
    (p : RealAdaptedGroup F (fun _ : Fin d => 1)) :
    realPolynomialSequence F d h (normalizedRealPolynomial F d p) =
      OriginalSameStepLinearizationOrbit.normalize (realPolynomialSequence F d h p) := by
  funext k
  change realAdaptedEvaluation F (k • h)
      (p * (realFiberInclusion F d
        (realFiberConstant F d (realAdaptedEvaluation F 0 p)))⁻¹) =
    realAdaptedEvaluation F (k • h) p *
      (realAdaptedEvaluation F ((0 : ℤ) • h) p)⁻¹
  rw [map_mul, map_inv, realFiberEvaluation_inclusion,
    realFiberEvaluation_constant, zero_zsmul]
  rfl

theorem realFiberSequence_difference (h : TimeTorus.Algebra d)
    (p : RealAdaptedGroup F (fun _ : Fin d => 1)) :
    realFiberSequence F d h (realDifferenceElement F d h p) =
      rightDifference (realPolynomialSequence F d h p) := by
  funext k
  change realFiberEvaluation F d (k • h) (realDifferenceElement F d h p) = _
  rw [realDifferenceElement_evaluation]
  change (realAdaptedEvaluation F (k • h) p)⁻¹ *
      realAdaptedEvaluation F (k • h + h) p =
    (realAdaptedEvaluation F (k • h) p)⁻¹ * realAdaptedEvaluation F ((k + 1) • h) p
  apply congrArg (fun x : Fin d → ℚ =>
    (realAdaptedEvaluation F (k • h) p)⁻¹ * realAdaptedEvaluation F x p)
  exact (by rw [add_zsmul, one_zsmul] : k • h + h = (k + 1) • h)

theorem realFiberSequence_constant (h : TimeTorus.Algebra d)
    (g : F.realification.Group) :
    realFiberSequence F d h (realFiberConstant F d g) = fun _ => g := by
  funext k
  exact realFiberEvaluation_constant F d (k • h) g

abbrev RealIntegerExtension (h : TimeTorus.Algebra d) :=
  RealFiberGroup F d ⋊[realIntegerTranslationAction F d h] Multiplicative ℤ

noncomputable def realPolynomialStep (h : TimeTorus.Algebra d)
    (p : RealAdaptedGroup F (fun _ : Fin d => 1)) :
    RealIntegerExtension F d h :=
  ⟨realDifferenceElement F d h (normalizedRealPolynomial F d p), Multiplicative.ofAdd 1⟩

noncomputable def realPolynomialBasepoint (h : TimeTorus.Algebra d)
    (p : RealAdaptedGroup F (fun _ : Fin d => 1)) :
    RealIntegerExtension F d h :=
  ⟨realFiberConstant F d (realAdaptedEvaluation F 0 p), 1⟩

/-- No coefficient-dependent operation remains in the readout: it is always
    plain evaluation at zero. -/
theorem realPolynomial_readout (h : TimeTorus.Algebra d)
    (p : RealAdaptedGroup F (fun _ : Fin d => 1)) (n : ℤ) :
    realFiberEvaluation F d 0
      ((realPolynomialStep F d h p ^ n) * realPolynomialBasepoint F d h p).left =
      realPolynomialSequence F d h p n := by
  have hd := realFiberSequence_difference F d h (normalizedRealPolynomial F d p)
  rw [realPolynomialSequence_normalized] at hd
  have hc : realFiberSequence F d h
      (realFiberConstant F d (realAdaptedEvaluation F 0 p)) =
      fun _ => realPolynomialSequence F d h p 0 := by
    change realFiberSequence F d h
      (realFiberConstant F d (realAdaptedEvaluation F 0 p)) =
      fun _ => realAdaptedEvaluation F ((0 : ℤ) • h) p
    rw [zero_zsmul]
    exact realFiberSequence_constant F d h (realAdaptedEvaluation F 0 p)
  exact realInteger_based_orbit F d h (realPolynomialSequence F d h p)
    (realDifferenceElement F d h (normalizedRealPolynomial F d p))
    (realFiberConstant F d (realAdaptedEvaluation F 0 p)) hd hc n

/-- The clock is exactly the integer time, including for negative powers. -/
theorem realPolynomial_clock (h : TimeTorus.Algebra d)
    (p : RealAdaptedGroup F (fun _ : Fin d => 1)) (n : ℤ) :
    ((realPolynomialStep F d h p ^ n) * realPolynomialBasepoint F d h p).right =
      Multiplicative.ofAdd n := by
  change SemidirectProduct.rightHom
    ((realPolynomialStep F d h p ^ n) * realPolynomialBasepoint F d h p) = _
  rw [map_mul, map_zpow]
  change (Multiplicative.ofAdd (1 : ℤ)) ^ n * 1 = Multiplicative.ofAdd n
  apply Multiplicative.toAdd.injective
  simp

end Hindman168.OriginalSameStepLinearization
