import Hindman168.MasterReplicaDualFormula

/-!
# Normalized dual products under the original master prime and shift laws

The local good-event probabilities are derived, and the numerator is the
proved actual variable-dimensional weighted quotient cube limit. Thus this
application does not assume numerator convergence or normalization. Fixed
local polynomial families are included by renaming in the global master
list with master arity independent of the number of replicas. Only the
renamed denominator list is replicated for the cube proof. Construction of
the correlation templates and later moments/clipping remain separate proof
obligations.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def masterPredictionBlockMask {m : ℕ} (F : MasterParameterFamily)
    (C : ℕ → Chain m) (label : ℕ → Fin m) (w : ℕ) (y : ℤ) : ℝ :=
  integerDivisorMask (tailMass (primorial w) ((C w).tailCutoffs (F.cutoff w) (label w))) y

theorem MasterParameterConditions.normalized_dual_product_tendsto {n r N m b d K : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0)
    (hb : 0 < b) (dim arity : Fin b → ℕ) (hd : ∀ q, dim q ≤ d) (hpos : ∀ q, 0 < dim q)
    (e : (Σ q, Fin (arity q)) ≃ Fin r)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N) (gap : ℕ → Fin b → Fin N)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htailgap : ∀ᶠ w in atTop, ∀ q, tail w ⊆ Finset.range (gap w q).val)
    (hgap : ∀ᶠ w in atTop, ∀ q, (gap w q).val ≤ (root w).val)
    (J : Fin K → ℕ) (hJ : ∀ a, 1 ≤ J a) (choice : ℕ → Fin b → Fin K)
    (tests : ∀ q, Finset (MvPolynomial (Fin (arity q)) ℤ))
    (den : ∀ q, MvPolynomial (Fin (arity q)) ℤ) (hden : ∀ q, den q ∈ tests q)
    (masterSlot : ∀ q, Fin (arity q) → Fin n) (hmasterSlot : ∀ q, Function.Injective (masterSlot q))
    (hinclude : ∀ q f, f ∈ tests q → MvPolynomial.rename (masterSlot q) f ∈ D)
    (ε : ℕ → ∀ q, (Fin (arity q) → ℕ) → ℝ)
    (hε : ∀ᶠ w in atTop, ∀ q x, |ε w q x| ≤ 1)
    (g : ℕ → ∀ q, (Fin (arity q) → ℕ) → CubeVertex (dim q) → ℤ → ℝ)
    (hg : ∀ᶠ w in atTop, ∀ q x S y, |g w q x S y| ≤ 1 + masterPredictionBlockMask F C label w y) :
    Tendsto (fun w => expectation (integerMass (F.cutoff w (root w).val) (primorial w))
      (fun y => (masterPredictionBlockMask F C label w y - 1) *
        ∏ q, masterReplicaGoodDualTest F dim arity gap J choice tests den ε g w q y))
      atTop (𝓝 0) := by
  let H w y := masterPredictionBlockMask F C label w y - 1
  let f q := replicaPolynomialLift e q (den q)
  let globalGap w j := replicaPrimeGap e (gap w) j
  let E w x := ∀ q, predictionLocalPrimeGoodEvent F (tests q) (den q) w ((replicaPrimeSampleEquiv arity e) x q)
  let G w x := predictionReplicaRowTests (H w) (g w) ((replicaPrimeSampleEquiv arity e) x)
  let ξ w x := ∏ q, ε w q ((replicaPrimeSampleEquiv arity e) x q)
  have htailprime : ∀ᶠ w in atTop, ∀ j, tail w ⊆ Finset.range (globalGap w j).val :=
    htailgap.mono (fun _ hw j => hw (e.symm j).1)
  have hdenzero (q : Fin b) : den q ≠ 0 := by
    intro hz
    apply hD (MvPolynomial.rename (masterSlot q) (den q)) (hinclude q (den q) (hden q))
    rw [hz, MvPolynomial.rename_zero]
  let polys := Finset.univ.image f
  have hf : ∀ q, f q ∈ polys := fun q => Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩
  have hpolys : ∀ p ∈ polys, p ≠ 0 := by
    intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    exact replicaPolynomialLift_nonzero e q (den q) (hdenzero q)
  have hslots : ∀ᶠ w in atTop, ∀ q j, j ∈ (f q).vars →
      (globalGap w j).val = (gap w q).val := Eventually.of_forall (fun w q j hj =>
        congrArg Fin.val (replicaPolynomialLift_vars_gap e (gap w) q (den q) j hj))
  have hnonzero : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => globalGap w j)).support,
      E w x → ∀ q, MvPolynomial.eval (fun j => (x j : ℤ)) (f q) ≠ 0 := by
    apply Eventually.of_forall
    intro w x _ hx q
    rw [show f q = replicaPolynomialLift e q (den q) from rfl, replicaPolynomialLift_eval]
    exact predictionLocalPrimeGoodEvent_den_nonzero F (tests q) (den q) (hden q) w _ (hx q)
  have hξ : ∀ᶠ w in atTop, ∀ x, |ξ w x| ≤ 1 := by
    filter_upwards [hε] with w hw
    intro x
    exact prediction_replica_prime_factor_bound (ε w) hw _
  have hroot : ∀ w x, G w x none = fun y => integerDivisorMask
      (masterPredictionBaseDivisorMass F C (fun w _ => label w) w (none : ReplicaCubeRow b d)) y - 1 := by
    intro w x
    rfl
  have hbound : ∀ᶠ w in atTop, ∀ x (row : Σ q, CubeVertex (dim q)) y,
      |G w x (some row) y| ≤ 1 + integerDivisorMask
        (masterPredictionBaseDivisorMass F C (fun w _ => label w) w (none : ReplicaCubeRow b d)) y := by
    filter_upwards [hg] with w hw
    intro x row y
    exact hw row.1 _ row.2 y
  let q₀ : Fin b := ⟨0, hb⟩
  let j₀ : Fin (dim q₀) := ⟨0, hpos q₀⟩
  let S₀ : CubeVertex (dim q₀) := ⟨{j₀}, Finset.singleton_nonempty _⟩
  let row₀ : VariableReplicaCubeRow dim := some ⟨q₀, S₀⟩
  have hrow₀ : row₀ ≠ none := Option.some_ne_none _
  have hfactor : ∀ᶠ w in atTop, ∀ _q : Fin b, (F.modulus w : ℕ) ∣ (F.modulus w : ℕ) :=
    Eventually.of_forall (fun _ _ => dvd_refl _)
  have hW : ∀ᶠ w in atTop, ∀ _q : Fin b, primorial w ∣ (F.modulus w : ℕ) :=
    hF.primorial_dvd_modulus.mono (fun _ hw _ => hw)
  have hnum : Tendsto (masterReplicaDualNumerator F root dim arity e gap J choice tests den H ε g)
      atTop (𝓝 0) :=
    hF.prediction_variable_quotient_weighted_cube_product_tendsto dim hd C hN label tail htail root gap
      globalGap J hJ choice htailroot htailgap htailprime hgap polys hpolys (fun w _ => (F.modulus w : ℕ))
      hfactor hW f hf (fun _ _ _ => 0) E hslots hnonzero G row₀ hrow₀ ξ hξ hroot hbound
  have hevent (q : Fin b) : Tendsto (fun w => event (masterReplicaLocalPrimeMass F arity gap w q)
      (predictionLocalPrimeGoodEvent F (tests q) (den q) w)) atTop (𝓝 1) :=
    hF.local_prime_good_event_tendsto_one (tests q) (den q) (hden q) (masterSlot q)
      (hmasterSlot q) (fun p hp => hinclude q p hp) (fun w => gap w q)
  have hp : Tendsto (fun w => ∏ q, event (masterReplicaLocalPrimeMass F arity gap w q)
      (predictionLocalPrimeGoodEvent F (tests q) (den q) w)) atTop (𝓝 1) := by
    simpa only [Finset.prod_const_one] using tendsto_finsetProd Finset.univ (fun q _ => hevent q)
  have hz := hnum.div hp (by norm_num : (1 : ℝ) ≠ 0)
  convert hz using 1
  · funext w
    exact master_replica_dual_normalized_formula F root dim arity e gap J choice tests den H ε g w
  · norm_num

end Hindman168
