import Hindman168.IntegerPredictionShortCubeStatistic
import Hindman168.MasterLocalGoodTupleLaw
import Hindman168.FiniteReplicaConditioning

/-! Exact prime-good sampling and integer short-cube statistics under a
bijective renaming of local prime slots. All original coefficients remain. -/

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

theorem conditioned_push_expectation {α β : Type*} (μ : Mass α)
    (p : α → β) (E : β → Prop) (f : β → ℝ) :
    expectation (conditionMass (μ.mapDomain p) E) f =
      expectation (conditionMass μ (fun x => E (p x))) (fun x => f (p x)) := by
  rw [expectation_conditionMass, expectation_conditionMass, event_map, expectation_push]

theorem primeSampleGood_rename_equiv {k n : ℕ} (e : Fin k ≃ Fin n)
    (T : Finset (MvPolynomial (Fin k) ℤ)) (x : Fin n → ℕ) :
    primeSampleGood (T.image (MvPolynomial.rename e)) x ↔
      primeSampleGood T (fun j => x (e j)) := by
  constructor
  · intro hx
    refine ⟨hx.1.comp e.injective, ?_⟩
    intro pol hpol
    have h := hx.2 (MvPolynomial.rename e pol) (Finset.mem_image.mpr ⟨pol, hpol, rfl⟩)
    simpa only [MvPolynomial.eval_rename, Function.comp_def] using h
  · intro hx
    refine ⟨?_, ?_⟩
    · intro i j hij
      have h := hx.1 (a₁ := e.symm i) (a₂ := e.symm j) (by simpa using hij)
      exact e.symm.injective h
    · intro pol hpol
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpol
      simpa only [MvPolynomial.eval_rename, Function.comp_def] using hx.2 p hp

theorem integerPredictionShortCubeStatistic_rename {k n : ℕ}
    (j : Fin k → Fin n) (w M R X d J : ℕ) (pol : MvPolynomial (Fin k) ℤ)
    (f : ℤ → ℝ) (x : Fin n → ℕ) :
    integerPredictionShortCubeStatistic w M R X d J (MvPolynomial.rename j pol) f x =
      integerPredictionShortCubeStatistic w M R X d J pol f (fun i => x (j i)) := by
  let H : ℕ → ℝ := fun P =>
    ∑ y ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℕ), integerMass X (primorial w) y *
      finiteHaarMean (fun v₀ : Fin d → Fin (R / P / J) =>
        finiteHaarMean (fun v₁ : Fin d → Fin (R / P / J) =>
          ∏ S : Finset (Fin d), f (y + (P : ℤ) *
            ∑ i ∈ S, (((v₁ i).val : ℤ) - (v₀ i).val))))
  change H (predictionCubeModulus w M (MvPolynomial.rename j pol) x).natAbs =
    H (predictionCubeModulus w M pol (fun i => x (j i))).natAbs
  apply congrArg H
  simp only [predictionCubeModulus, MvPolynomial.eval_rename, Function.comp_def]

theorem renamed_primeGood_shortCube_expectation {k n : ℕ} (e : Fin k ≃ Fin n)
    (T : Finset (MvPolynomial (Fin k) ℤ)) (A B w M R X d J : ℕ)
    (pol : MvPolynomial (Fin k) ℤ) (f : ℤ → ℝ) :
    expectation (conditionMass (primeIndependentMass n A B)
      (primeSampleGood (T.image (MvPolynomial.rename e)))) (fun x =>
        |integerPredictionShortCubeStatistic w M R X d J (MvPolynomial.rename e pol) f x|) =
      expectation (conditionMass (primeIndependentMass k A B) (primeSampleGood T)) (fun x =>
        |integerPredictionShortCubeStatistic w M R X d J pol f x|) := by
  have hlaw : (primeIndependentMass n A B).mapDomain (fun x j => x (e j)) =
      primeIndependentMass k A B := piMass_reindex _ e
  have hgood : (fun x => primeSampleGood T (fun j => x (e j))) =
      primeSampleGood (T.image (MvPolynomial.rename e)) := by
    funext x
    exact propext (primeSampleGood_rename_equiv e T x).symm
  rw [← hlaw, conditioned_push_expectation, hgood]
  apply congrArg (expectation (conditionMass (primeIndependentMass n A B)
    (primeSampleGood (T.image (MvPolynomial.rename e)))))
  funext x
  rw [integerPredictionShortCubeStatistic_rename]

end Hindman168
