import Hindman168.PredictionQuotientLengths

/-!
# Original prediction cube limit with fully specified quotient lengths

Each polynomial uses only prime slots from its replica gap. Actual prime
support and smooth-factor absorption give a polynomial denominator cap.
The interval lengths are R/(J|M_q|); lower growth and displacements are
proved, rather than supplied as application hypotheses. The retained
prime-only good event excludes zero polynomial values without renormalizing.
This fixed-dimension result still awaits full dual-test instantiation.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

theorem MasterParameterConditions.prediction_quotient_cube_product_tendsto
    {n N m r b d h L : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F)
    (dir : Fin h → Fin b × CubeVertex d) (hdir : Function.Bijective dir)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → ReplicaCubeRow b d → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, ∀ base, (C w).tail (label w base) ⊆ tail w)
    (root : ℕ → Fin N) (replicaGap : ℕ → Fin b → Fin N)
    (primeGap : ℕ → Fin r → Fin L) (J : ℕ) (hJ : 1 ≤ J)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htailreplica : ∀ᶠ w in atTop, ∀ q, tail w ⊆ Finset.range (replicaGap w q).val)
    (htailprime : ∀ᶠ w in atTop, ∀ j, tail w ⊆ Finset.range (primeGap w j))
    (hgap : ∀ᶠ w in atTop, ∀ q, (replicaGap w q).val ≤ (root w).val)
    (polys : Finset (MvPolynomial (Fin r) ℤ)) (hpolys : ∀ p ∈ polys, p ≠ 0)
    (s : ℕ → Fin b → ℕ)
    (hfactor : ∀ᶠ w in atTop, ∀ q, s w q ∣ (F.modulus w : ℕ))
    (hW : ∀ᶠ w in atTop, ∀ q, primorial w ∣ s w q)
    (f : Fin b → MvPolynomial (Fin r) ℤ) (hf : ∀ q, f q ∈ polys)
    (A : ℕ → (Fin r → ℕ) → Fin b × Fin d × Bool → ℤ)
    (E : ℕ → (Fin r → ℕ) → Prop)
    (hslots : ∀ᶠ w in atTop, ∀ q j, j ∈ (f q).vars →
      (primeGap w j).val = (replicaGap w q).val)
    (hnonzero : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      E w x → ∀ q, MvPolynomial.eval (fun j => (x j : ℤ)) (f q) ≠ 0)
    (G : ℕ → (Fin r → ℕ) → ReplicaCubeRow b d → ℤ → ℝ)
    (hroot : ∀ w x, G w x none = fun t =>
      integerDivisorMask (masterPredictionBaseDivisorMass F C label w none) t - 1)
    (hbound : ∀ᶠ w in atTop, ∀ x i t, |G w x (some (dir i)) t| ≤
      1 + integerDivisorMask (masterPredictionBaseDivisorMass F C label w (some (dir i))) t) :
    Tendsto (masterPredictionOriginalCubeAverage F root (fun w j => primeGap w j) s f A (predictionQuotientLength F replicaGap J s f) E G)
      atTop (𝓝 0) := by
  let k q := J + integerPolynomialCoeffSize (f q) + (f q).totalDegree + 1
  let T := predictionQuotientLength F replicaGap J s f
  let e (w : ℕ) (_ : Fin b) := Classical.choose (hF.smooth_modulus w)
  have hs : ∀ᶠ w in atTop, ∀ q, s w q ∣ primorial w ^ e w q := by
    filter_upwards [hfactor] with w hw
    intro q
    have hp := Classical.choose_spec (hF.smooth_modulus w)
    simpa only [e, ← hp] using hw q
  have hcap : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      ∀ q, J * (predictionCubeModulus w (s w q) (f q) x).natAbs ≤
        ((F.pool w (replicaGap w q).val).upper + F.auxiliary w (replicaGap w q).val) ^ k q := by
    filter_upwards [hslots, hfactor] with w hslot hfact
    intro x hx q
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
    exact predictionQuotientLength_lower F replicaGap J s f w x q (k q)
      (by omega) (hn x hx he q) (hc x hx q)
  have hM : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      E w x → ∀ q, (primorial w : ℤ) ∣ predictionCubeModulus w (s w q) (f q) x :=
    hW.mono (fun w hw x _ _ q => predictionCubeModulus_W_divisible w (s w q) (f q) x (hw q))
  have hR : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      E w x → ∀ q, |(predictionCubeModulus w (s w q) (f q) x : ℝ)| * T w x q ≤
        F.gap w (replicaGap w q).val := Eventually.of_forall (fun w x _ _ q =>
          predictionQuotientLength_displacement F replicaGap J s f w x q hJ)
  exact hF.prediction_original_cube_product_tendsto dir hdir C hN label tail htail root
    replicaGap primeGap k htailroot htailreplica htailprime hgap polys hpolys s e hs f hf
    A T E hT hM hR G hroot hbound

end Hindman168
