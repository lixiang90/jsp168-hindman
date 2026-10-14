import Hindman168.MasterPredictionOriginalMajorantMean
import Hindman168.MasterPredictionVariableQuotientLimit

/-!
# Actual quotient-length one-plus cube means

Sparse prime slots and original prime support bound each denominator.
The finite positive J family gives a fixed polynomial exponent. Quotient
length growth, smooth factors and all subset means are then derived.
-/

namespace Hindman168

open Filter
open FiniteMass
open scoped BigOperators Topology Classical

theorem MasterParameterConditions.prediction_quotient_majorant_mean_tendsto
    {n N m r b d L K : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → ReplicaCubeRow b d → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, ∀ row, (C w).tail (label w row) ⊆ tail w)
    (root : ℕ → Fin N) (replicaGap : ℕ → Fin b → Fin N)
    (primeGap : ℕ → Fin r → Fin L) (J : Fin K → ℕ) (hJ : ∀ a, 1 ≤ J a)
    (choice : ℕ → Fin b → Fin K)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htailreplica : ∀ᶠ w in atTop, ∀ q, tail w ⊆ Finset.range (replicaGap w q).val)
    (htailprime : ∀ᶠ w in atTop, ∀ j, tail w ⊆ Finset.range (primeGap w j))
    (polys : Finset (MvPolynomial (Fin r) ℤ)) (hpolys : ∀ p ∈ polys, p ≠ 0)
    (s : ℕ → Fin b → ℕ)
    (hfactor : ∀ᶠ w in atTop, ∀ q, s w q ∣ (F.modulus w : ℕ))
    (f : Fin b → MvPolynomial (Fin r) ℤ) (hf : ∀ q, f q ∈ polys)
    (A : ℕ → (Fin r → ℕ) → Fin b × Fin d × Bool → ℤ)
    (E : ℕ → (Fin r → ℕ) → Prop)
    (hslots : ∀ᶠ w in atTop, ∀ q j, j ∈ (f q).vars →
      (primeGap w j).val = (replicaGap w q).val)
    (hnonzero : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      E w x → ∀ q, MvPolynomial.eval (fun j => (x j : ℤ)) (f q) ≠ 0) :
    Tendsto (fun w => masterPredictionOriginalMajorantAverage F C label root
      (fun w j => primeGap w j) s f A (predictionVariableQuotientLength F replicaGap J choice s f) E w -
      (2 : ℝ) ^ Fintype.card (ReplicaCubeRow b d) *
        event (masterPrimeSlotsMass F w (fun j => primeGap w j)) (E w)) atTop (𝓝 0) := by
  let Jmax := ∑ a, J a
  have hJmax (a : Fin K) : J a ≤ Jmax := Finset.single_le_sum
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  let k q := Jmax + integerPolynomialCoeffSize (f q) + (f q).totalDegree + 1
  let T := predictionVariableQuotientLength F replicaGap J choice s f
  let e (w : ℕ) (_ : Fin b) := Classical.choose (hF.smooth_modulus w)
  have hs : ∀ᶠ w in atTop, ∀ q, s w q ∣ primorial w ^ e w q := by
    filter_upwards [hfactor] with w hw
    intro q
    have hp := Classical.choose_spec (hF.smooth_modulus w)
    simpa only [e, ← hp] using hw q
  have hcap : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      ∀ q, J (choice w q) * (predictionCubeModulus w (s w q) (f q) x).natAbs ≤
        ((F.pool w (replicaGap w q).val).upper + F.auxiliary w (replicaGap w q).val) ^ k q := by
    filter_upwards [hslots, hfactor] with w hslot hfact
    intro x hx q
    apply (Nat.mul_le_mul_right (predictionCubeModulus w (s w q) (f q) x).natAbs
      (hJmax (choice w q))).trans
    apply predictionCubeModulus_polynomial_cap
    · have hh := F.auxiliary_ge_two w (replicaGap w q).val
      omega
    · have hsle := Nat.le_of_dvd (F.modulus w).property (hfact q)
      have hm : (F.modulus w : ℕ) ≤ F.auxiliary w (replicaGap w q).val := by
        unfold MasterParameterFamily.auxiliary
        omega
      exact hsle.trans (hm.trans (Nat.le_add_left _ _))
    · intro j hj
      have hv := masterPrimeSlotsMass_support F w (fun j => primeGap w j) hx j
      rw [hslot q j hj] at hv
      omega
  have hne : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      E w x → ∀ q, predictionCubeModulus w (s w q) (f q) x ≠ 0 := by
    filter_upwards [hfactor, hnonzero] with w hfact hn
    intro x hx he q
    exact predictionCubeModulus_nonzero w (s w q) (f q) x
      (Nat.pos_of_dvd_of_pos (hfact q) (F.modulus w).property) (hn x hx he q)
  have hT : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      E w x → ∀ q, masterShiftLengthLowerBound F w (replicaGap w q).val (k q) ≤ T w x q := by
    filter_upwards [hcap, hne] with w hc hn
    intro x hx he q
    exact predictionQuotientLength_lower F replicaGap (J (choice w q)) s f w x q (k q)
      (lt_of_lt_of_le Nat.zero_lt_one (hJ _)) (hn x hx he q) (hc x hx q)
  exact hF.prediction_original_majorant_mean_tendsto C hN label tail htail root
    replicaGap primeGap k htailroot htailreplica htailprime polys hpolys s e hs f hf
    A T E hT

end Hindman168
