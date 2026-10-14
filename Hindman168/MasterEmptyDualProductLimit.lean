import Hindman168.FiniteEmptyCoordinateLaw

/-!
# The empty dual product: actual original mask mean one

The b=0 application has no prime or shift coordinates and no nonroot
weight to absorb a factor into. Exact empty-coordinate laws identify the
existing unweighted cube theorem with the original harmonic mask mean.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem MasterParameterConditions.empty_dual_product_tendsto {n N m : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val) :
    Tendsto (fun w => expectation (integerMass (F.cutoff w (root w).val) (primorial w))
      (fun y => masterPredictionBlockMask F C label w y - 1)) atTop (𝓝 0) := by
  let dim : Fin 0 → ℕ := fun _ => 0
  let gap : ℕ → Fin 0 → Fin N := fun _ q => Fin.elim0 q
  let k : Fin 0 → ℕ := fun _ => 0
  let s : ℕ → Fin 0 → ℕ := fun _ _ => 1
  let e : ℕ → Fin 0 → ℕ := fun _ _ => 0
  let f : Fin 0 → MvPolynomial (Fin 0) ℤ := fun q => Fin.elim0 q
  let A : ℕ → (Fin 0 → ℕ) → VariableReplicaCubeColumn dim → ℤ := fun _ _ _ => 0
  let T : ℕ → (Fin 0 → ℕ) → Fin 0 → ℕ := fun _ _ _ => 0
  let E : ℕ → (Fin 0 → ℕ) → Prop := fun _ _ => True
  let G (w : ℕ) (_x : Fin 0 → ℕ) : VariableReplicaCubeRow dim → ℤ → ℝ
    | none => fun y => masterPredictionBlockMask F C label w y - 1
    | some row => Fin.elim0 row.1
  have hdim : ∀ q, dim q ≤ 0 := fun q => Fin.elim0 q
  have htailgap : ∀ᶠ w in atTop, ∀ q, tail w ⊆ Finset.range (gap w q).val :=
    Eventually.of_forall (fun _ q => Fin.elim0 q)
  have hgap : ∀ᶠ w in atTop, ∀ q, (gap w q).val ≤ (root w).val :=
    Eventually.of_forall (fun _ q => Fin.elim0 q)
  have hs : ∀ᶠ w in atTop, ∀ q, s w q ∣ primorial w ^ e w q :=
    Eventually.of_forall (fun _ q => Fin.elim0 q)
  have hf : ∀ q, f q ∈ (∅ : Finset (MvPolynomial (Fin 0) ℤ)) := fun q => Fin.elim0 q
  have hpolys : ∀ p ∈ (∅ : Finset (MvPolynomial (Fin 0) ℤ)), p ≠ 0 := by simp
  have hT : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => gap w j)).support,
      E w x → ∀ q, masterShiftLengthLowerBound F w (gap w q).val (k q) ≤ T w x q :=
    Eventually.of_forall (fun _ _ _ _ q => Fin.elim0 q)
  have hM : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => gap w j)).support,
      E w x → ∀ q, (primorial w : ℤ) ∣ predictionCubeModulus w (s w q) (f q) x :=
    Eventually.of_forall (fun _ _ _ _ q => Fin.elim0 q)
  have hR : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => gap w j)).support,
      E w x → ∀ q, |(predictionCubeModulus w (s w q) (f q) x : ℝ)| * T w x q ≤ F.gap w (gap w q).val :=
    Eventually.of_forall (fun _ _ _ _ q => Fin.elim0 q)
  have hroot : ∀ w x, G w x none = fun y => integerDivisorMask
      (masterPredictionBaseDivisorMass F C (fun w _ => label w) w (none : ReplicaCubeRow 0 0)) y - 1 := by
    intro w x
    rfl
  have hbound : ∀ᶠ w in atTop, ∀ x (row : Σ q, CubeVertex (dim q)) y,
      |G w x (some row) y| ≤ 1 + integerDivisorMask
        (masterPredictionBaseDivisorMass F C (fun w _ => label w) w (none : ReplicaCubeRow 0 0)) y :=
    Eventually.of_forall (fun _ _ row _ => Fin.elim0 row.1)
  have h := hF.prediction_variable_cube_product_tendsto dim hdim C hN label tail htail root gap gap k
    htailroot htailgap htailgap hgap ∅ hpolys s e hs f hf A T E hT hM hR G hroot hbound
  have hid (w : ℕ) : masterPredictionVariableCubeAverage F root (fun w j => gap w j) s f A T E G w =
      expectation (integerMass (F.cutoff w (root w).val) (primorial w))
        (fun y => masterPredictionBlockMask F C label w y - 1) := by
    unfold masterPredictionVariableCubeAverage masterPrimeSlotsMass
    rw [piMass_empty_expectation]
    simp only [E, if_pos trivial, variable_cube_empty_row_product]
    exact variable_cube_empty_root_average dim _ _ _ _ _
  convert h using 1
  funext w
  exact (hid w).symm

end Hindman168
