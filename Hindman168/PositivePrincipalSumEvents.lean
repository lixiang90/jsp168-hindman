import Hindman168.PositivePrincipalSumScales
import Hindman168.PositivePrincipalSumAlignment
import Hindman168.FiniteScaleColorIndices
import Hindman168.HarmonicCutoffBands

/-!
# The original alignment event and samplewise selection

The event is exactly the simultaneous adding-pair implication for one
scale vector and every block, color and finite set of earlier adding
blocks. Calibration failures use the original principal probabilities.
-/

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

abbrev PrincipalSumBlock (n : ℕ) :=
  {p : Finset (Fin n) × Fin n // p.1.Nonempty ∧ ∀ k ∈ p.1, k < p.2}

abbrev PrincipalSumCalibrationIndex (n : ℕ) (A : Finset ℚ) (r : ℕ) :=
  PrincipalSumBlock n × ScaleColorIndex A r

abbrev PrincipalSumCountIndex {n : ℕ} (m : ℕ) (B : Finset (Fin n → ℚ)) (r : ℕ) :=
  B × PrincipalCoordinateChain n (m+1) × Fin r

def principalSumGamma {n m r : ℕ} (B : Finset (Fin n → ℚ)) (A : Finset ℚ)
    (hclosed : FiniteScaleClosure B A) (q : PrincipalSumCountIndex m B r)
    (i : Fin (m+1)) : ScaleColorIndex A r :=
  scaleBlockColorIndex B A hclosed q.1.val q.1.property (q.2.1.block i)
    (by simp [PrincipalCoordinateChain.block]) q.2.2

def PrincipalSumAlignmentEvent {n r : ℕ} (M : ℕ) (e : Fin (2*n) ↪o ℕ)
    (B : Finset (Fin n → ℚ)) (A : Finset ℚ) (hclosed : FiniteScaleClosure B A)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (θ : ℝ) (w : ℕ) (x : Fin n → ℕ) : Prop :=
  ∃ b : B, ∀ κ : Fin r, PrincipalAddingAlignment M e b.val w
    (fun T i => S T i (scaleBlockColorIndex B A hclosed b.val b.property
      (insert i T) (Finset.insert_nonempty _ _) κ) w) θ x

/-- Original selected harmonic supports have positive natural coordinates. -/
theorem MasterParameterConditions.principal_raw_support_positive
    {d n M : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (e : Fin (2*n) ↪o ℕ) (w : ℕ) (x : Fin n → ℕ)
    (hx : x ∈ (selectedPrincipalRawMass e F w).support) (i : Fin n) : 0 < x i := by
  have hn := Finsupp.mem_support_iff.mp hx
  rw [selectedPrincipalRawMass, piMass_apply] at hn
  have hcoord := Finsupp.mem_support_iff.mpr
    (Finset.prod_ne_zero_iff.mp hn i (Finset.mem_univ i))
  have hb := (Finset.mem_Ico.mp (Finset.mem_filter.mp (rawMass_support_window _ _ hcoord)).1).1
  exact (hF.cutoff_positive w _).trans_le hb

/-- Product-chain selection, absence of actual calibration failures, and
the original adding-pair event together select a large actual model term. -/
theorem principal_alignment_good_sample_selects_model {n m r M : ℕ}
    (hselect : ∀ χ : ℕ → Fin r, ∀ x : Fin n → ℕ,
      ∃ C : PrincipalCoordinateChain n (m+1), ∃ κ : Fin r,
        ∀ J : Finset (Fin (m+1)), J.Nonempty → χ (∏ i ∈ J, C.sampleProducts x i) = κ)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (B : Finset (Fin n → ℚ)) (A : Finset ℚ) (hclosed : FiniteScaleClosure B A)
    (χ : ℕ → Fin r)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (w : ℕ) (x : Fin n → ℕ)
    (hx : ∀ i, 0 < x i)
    (hcoeff : ∀ b : B, ∀ k, 0 < principalIndividualCoefficient M e b.val w k ∧
      (masterScale (primorial w) w M {energyPrincipal e k} : ℚ) * b.val k =
        principalIndividualCoefficient M e b.val w k)
    (halign : PrincipalSumAlignmentEvent M e B A hclosed S θ w x)
    (hgood : ∀ j : PrincipalSumCalibrationIndex n A r,
      ¬ (let z : ℤ := (principalSubsetProduct (insert j.1.val.2 j.1.val.1) x : ℤ)
        0 < z ∧ χ (principalBlockCoefficient M e j.1.val.1 j.1.val.2
          (scaleColorFactor A r j.2) w * z.toNat) = scaleColorValue A r j.2 ∧
          S j.1.val.1 j.1.val.2 j.2 w z ≤ 2*θ)) :
    ∃ q : PrincipalSumCountIndex m B r,
      θ ^ Fintype.card (NonemptyColumnSubset (m+1)) ≤
        principalBoundedCountIntegrand q.2.1 M e
          (fun i => scaleColorFactor A r (principalSumGamma B A hclosed q i)) w
          (fun i => S (q.2.1.tail i) (q.2.1.pivot i) (principalSumGamma B A hclosed q i) w)
          (principalColorProductMask q.2.1 M e
            (fun i => scaleColorFactor A r (principalSumGamma B A hclosed q i)) χ q.2.2 w)
          (fun i => (q.2.1.sampleProducts x i : ℤ)) := by
  obtain ⟨b, hb⟩ := halign
  obtain ⟨C, κ, hprod⟩ := principal_scaled_product_chain_selection hselect e b.val w
    (fun k => (hcoeff b k).2) χ x
  let q : PrincipalSumCountIndex m B r := (b, C, κ)
  let a : Fin (m+1) → ℚ := fun i => ∏ k ∈ C.block i, b.val k
  let rows : Fin (m+1) → ℤ → ℝ :=
    fun i => S (C.tail i) (C.pivot i) (principalSumGamma B A hclosed q i) w
  have hz (i : Fin (m+1)) : 0 < C.sampleProducts x i := Finset.prod_pos (fun k _ => hx k)
  have hc (i : Fin (m+1)) : 0 < C.coefficient M e a w i := by
    rw [principal_block_coefficient_product C e b.val w (fun k => (hcoeff b k).2)]
    exact Finset.prod_pos (fun k _ => (hcoeff b k).1)
  have hcenters (i : Fin (m+1)) : 2*θ < rows i (C.sampleProducts x i) := by
    by_contra hn
    have hle := le_of_not_gt hn
    let j : PrincipalSumCalibrationIndex n A r :=
      (⟨(C.tail i, C.pivot i), C.tail_nonempty i, C.tails_before_pivots i i⟩,
        principalSumGamma B A hclosed q i)
    apply hgood j
    refine ⟨by exact_mod_cast hz i, ?_, hle⟩
    change χ (C.coefficient M e a w i * C.sampleProducts x i) = κ
    simpa only [Finset.prod_singleton] using hprod {i} (by simp)
  refine ⟨q, ?_⟩
  apply principal_model_integrand_lower_bound_of_alignment C e heM a χ κ w rows
    (C.sampleProducts x) hz θ hθ hθ1 hcenters ?_ hprod
  intro V _ hcenter
  exact principal_adding_alignment_chain_rows C e b.val w
    (fun T i => S T i (scaleBlockColorIndex B A hclosed b.val b.property
      (insert i T) (Finset.insert_nonempty _ _) κ) w) θ x hc (hb κ) V hcenter

end Hindman168
