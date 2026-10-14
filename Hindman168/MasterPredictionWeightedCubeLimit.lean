import Hindman168.PredictionPrimeFactors

/-!
# Prime-weighted original cube limit for arbitrary replica dimensions

The varying bounded prime-only factor is absorbed once into a nonroot test.
No convergence of that factor and no event normalization are assumed.
The empty-product case has factor one and is already covered by the
unweighted original cube theorem.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def masterPredictionVariableWeightedCubeAverage {N r b : ℕ} {dim : Fin b → ℕ}
    (F : MasterParameterFamily) (root : ℕ → Fin N) (primeGap : ℕ → Fin r → ℕ)
    (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (A : ℕ → (Fin r → ℕ) → VariableReplicaCubeColumn dim → ℤ)
    (T : ℕ → (Fin r → ℕ) → Fin b → ℕ) (E : ℕ → (Fin r → ℕ) → Prop)
    (G : ℕ → (Fin r → ℕ) → VariableReplicaCubeRow dim → ℤ → ℝ)
    (ξ : ℕ → (Fin r → ℕ) → ℝ) (w : ℕ) : ℝ :=
  expectation (masterPrimeSlotsMass F w (primeGap w)) (fun x => if E w x then
    expectation (piMass (variablePredictionOriginalColumnMass (F.cutoff w (root w).val)
      (primorial w) (A w x) (T w x)))
      (fun z => ξ w x * ∏ row, G w x row (variableReplicaCubeEval
        (fun q => predictionCubeModulus w (s w q) (f q) x) row z)) else 0)

theorem MasterParameterConditions.prediction_variable_weighted_cube_product_tendsto
    {n N m r b d L : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F)
    (dim : Fin b → ℕ) (hd : ∀ q, dim q ≤ d)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N) (replicaGap : ℕ → Fin b → Fin N)
    (primeGap : ℕ → Fin r → Fin L) (k : Fin b → ℕ)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htailreplica : ∀ᶠ w in atTop, ∀ q, tail w ⊆ Finset.range (replicaGap w q).val)
    (htailprime : ∀ᶠ w in atTop, ∀ j, tail w ⊆ Finset.range (primeGap w j))
    (hgap : ∀ᶠ w in atTop, ∀ q, (replicaGap w q).val ≤ (root w).val)
    (polys : Finset (MvPolynomial (Fin r) ℤ)) (hpolys : ∀ p ∈ polys, p ≠ 0)
    (s : ℕ → Fin b → ℕ) (e : ℕ → Fin b → ℕ)
    (hs : ∀ᶠ w in atTop, ∀ q, s w q ∣ primorial w ^ e w q)
    (f : Fin b → MvPolynomial (Fin r) ℤ) (hf : ∀ q, f q ∈ polys)
    (A : ℕ → (Fin r → ℕ) → VariableReplicaCubeColumn dim → ℤ)
    (T : ℕ → (Fin r → ℕ) → Fin b → ℕ) (E : ℕ → (Fin r → ℕ) → Prop)
    (hT : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      E w x → ∀ q, masterShiftLengthLowerBound F w (replicaGap w q).val (k q) ≤ T w x q)
    (hM : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      E w x → ∀ q, (primorial w : ℤ) ∣ predictionCubeModulus w (s w q) (f q) x)
    (hR : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      E w x → ∀ q,
        |(predictionCubeModulus w (s w q) (f q) x : ℝ)| * T w x q ≤ F.gap w (replicaGap w q).val)
    (G : ℕ → (Fin r → ℕ) → VariableReplicaCubeRow dim → ℤ → ℝ)
    (row0 : VariableReplicaCubeRow dim) (hrow0 : row0 ≠ none)
    (ξ : ℕ → (Fin r → ℕ) → ℝ) (hξ : ∀ᶠ w in atTop, ∀ x, |ξ w x| ≤ 1)
    (hroot : ∀ w x, G w x none = fun t =>
      integerDivisorMask (masterPredictionBaseDivisorMass F C (fun w _ => label w) w (none : ReplicaCubeRow b d)) t - 1)
    (hbound : ∀ᶠ w in atTop, ∀ x (row : Σ q : Fin b, CubeVertex (dim q)) t,
      |G w x (some row) t| ≤ 1 + integerDivisorMask
        (masterPredictionBaseDivisorMass F C (fun w _ => label w) w (none : ReplicaCubeRow b d)) t) :
    Tendsto (masterPredictionVariableWeightedCubeAverage F root (fun w j => primeGap w j) s f A T E G ξ)
      atTop (𝓝 0) := by
  let G' w x := oneRowPrimeFactor row0 (ξ w x) (G w x)
  have hr : ∀ w x, G' w x none = fun t =>
      integerDivisorMask (masterPredictionBaseDivisorMass F C (fun w _ => label w) w
        (none : ReplicaCubeRow b d)) t - 1 := by
    intro w x
    rw [show G' w x none = G w x none from oneRowPrimeFactor_other row0 none _ _ (Ne.symm hrow0)]
    exact hroot w x
  have hb : ∀ᶠ w in atTop, ∀ x (row : Σ q : Fin b, CubeVertex (dim q)) t,
      |G' w x (some row) t| ≤ 1 + integerDivisorMask
        (masterPredictionBaseDivisorMass F C (fun w _ => label w) w (none : ReplicaCubeRow b d)) t := by
    filter_upwards [hbound, hξ] with w hw hξw
    intro x row t
    exact oneRowPrimeFactor_bound row0 (some row) (ξ w x) (G w x) _ (hξw x) (hw x row) t
  have hz := hF.prediction_variable_cube_product_tendsto dim hd C hN label tail htail root
    replicaGap primeGap k htailroot htailreplica htailprime hgap polys hpolys s e hs f hf
    A T E hT hM hR G' hr hb
  convert hz using 1
  funext w
  simp only [masterPredictionVariableCubeAverage, masterPredictionVariableWeightedCubeAverage,
    G', oneRowPrimeFactor_product]

end Hindman168
