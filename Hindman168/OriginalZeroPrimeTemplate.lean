import Hindman168.OriginalDualTemplates
import Hindman168.FiniteEmptyCoordinateLaw

/-!
# The original extra cube type with no prime variables and modulus M

The local list and denominator are exactly {1} and 1. Its local good event
is identically true at every positive master exponent. The separately
conditioned empty prime law retains unit mass, and the dual becomes exactly
one original uniform-shift cube, with no prime average or normalization.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem conditionMass_of_everywhere_true {α : Type*} (μ : Mass α) (E : α → Prop)
    (hE : ∀ x, E x) (hμ : total μ = 1) : conditionMass μ E = μ := by
  have hev : event μ E = 1 := by
    simpa only [event, total, if_pos (hE _)] using hμ
  ext x
  rw [conditionMass_apply, if_pos (hE x), hev, div_one]

end Hindman168.FiniteMass

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def originalZeroPrimeTemplate {n N K : ℕ} (d : ℕ)
    (gap : ℕ → Fin N) (choice : ℕ → Fin K) : OriginalDualTemplate n N K where
  dimension := d
  arity := 0
  gap := gap
  choice := choice
  tests := {1}
  denominator := 1
  denominator_mem := Finset.mem_singleton_self 1
  masterSlot := Fin.elim0
  masterSlot_injective := Function.injective_of_subsingleton _

theorem originalZeroPrimeTemplate_conditions {n N K : ℕ}
    (d Dmax : ℕ) (hd : 0 < d) (hmax : d ≤ Dmax)
    (gap : ℕ → Fin N) (choice : ℕ → Fin K)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hone : 1 ∈ D)
    (tail : ℕ → Finset ℕ) (root : ℕ → Fin N)
    (htail : ∀ᶠ w in atTop, tail w ⊆ Finset.range (gap w).val)
    (hgap : ∀ᶠ w in atTop, (gap w).val ≤ (root w).val) :
    OriginalDualTemplateConditions (originalZeroPrimeTemplate d gap choice) D Dmax tail root := by
  refine ⟨hd, hmax, ?_, htail, hgap⟩
  intro f hf
  change f ∈ ({1} : Finset (MvPolynomial (Fin 0) ℤ)) at hf
  have hf1 : f = 1 := Finset.mem_singleton.mp hf
  subst f
  change MvPolynomial.rename (Fin.elim0 : Fin 0 → Fin n) 1 ∈ D
  simpa only [map_one] using hone

theorem zero_prime_local_good_event (F : MasterParameterFamily) (w : ℕ)
    (he : 0 < F.exponent w) (x : Fin 0 → ℕ) :
    predictionLocalPrimeGoodEvent F {1} 1 w x := by
  refine ⟨⟨Function.injective_of_subsingleton x, ?_⟩, ?_⟩
  · intro f hf
    have hf1 : f = 1 := Finset.mem_singleton.mp hf
    subst f
    simp
  · rintro ⟨p, _hp, hp⟩
    have hd : p.val ^ F.exponent w ∣ 1 := by
      have hz : ((p.val ^ F.exponent w : ℕ) : ℤ) ∣ (1 : ℤ) := by
        simpa only [map_one] using hp
      exact_mod_cast hz
    have hlt : 1 < p.val ^ F.exponent w := one_lt_pow' p.property.one_lt he.ne'
    have heq := Nat.dvd_one.mp hd
    omega

theorem zero_prime_local_good_mass (F : MasterParameterFamily) (w A B : ℕ)
    (he : 0 < F.exponent w) :
    event (primeIndependentMass 0 A B) (predictionLocalPrimeGoodEvent F {1} 1 w) = 1 := by
  have ht : total (primeIndependentMass 0 A B) = 1 := by
    simp [primeIndependentMass, piMass_total]
  simpa only [event, total, if_pos (zero_prime_local_good_event F w he _)] using ht

theorem zero_prime_conditioned_mass (F : MasterParameterFamily) (w A B : ℕ)
    (he : 0 < F.exponent w) :
    conditionMass (primeIndependentMass 0 A B) (predictionLocalPrimeGoodEvent F {1} 1 w) =
      primeIndependentMass 0 A B := by
  apply conditionMass_of_everywhere_true _ _ (zero_prime_local_good_event F w he)
  simp [primeIndependentMass, piMass_total]

theorem predictionCubeModulus_one {a : ℕ} (w s : ℕ) (x : Fin a → ℕ) :
    predictionCubeModulus w s 1 x = (s : ℤ) := by
  simp [predictionCubeModulus, roughPartNat]

theorem originalZeroPrimeTemplate_dual {n N K : ℕ} (d : ℕ)
    (gap : ℕ → Fin N) (choice : ℕ → Fin K) (F : MasterParameterFamily)
    (J : Fin K → ℕ) (u : OriginalSingleDualInput 0 d) (w : ℕ) (y : ℤ)
    (he : 0 < F.exponent w) :
    (originalZeroPrimeTemplate (n := n) d gap choice).dual F J u w y =
      expectation (piMass (fun _ : Fin d × Bool => uniformIntervalMass 0
        (F.gap w (gap w).val / (J (choice w) * (F.modulus w : ℕ)))))
        (fun z => u.epsilon (fun i => isEmptyElim i) * ∏ S : CubeVertex d,
          u.vertexTest (fun i => isEmptyElim i) S
            (y + (F.modulus w : ℤ) * ∑ j ∈ S.val, (z (j, true) - z (j, false)))) := by
  unfold OriginalDualTemplate.dual
  dsimp only [originalZeroPrimeTemplate]
  unfold masterSingleGoodDualTest
  rw [zero_prime_conditioned_mass F w _ _ he]
  unfold predictionSingleDualTest
  rw [show primeIndependentMass 0 _ _ = piMass (fun _ : Fin 0 =>
    primePoolMass (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper) from rfl,
    piMass_empty_expectation]
  simp only [predictionCubeModulus_one, Int.natAbs_natCast]

end Hindman168
