import Hindman168.FinitePivotCoordinates
import Hindman168.FiniteReplicaJointLaw
import Hindman168.AlignmentRawArrayStability
import Hindman168.SelectedAlignmentRouteCell

/-! Exact original full-raw disintegration into all nonpivot coordinates
and the signed harmonic pivot kernel. The outside coordinates are never
replaced by dummy supported points. -/
namespace Hindman168
open Filter FiniteMass
open scoped Topology Classical

noncomputable def selectedAlignmentOutsideRawMass {M : ℕ}
    (F : MasterParameterFamily) (w : ℕ) (i : Fin M) :
    Mass ({j : Fin M // j ≠ i} → ℕ) := by
  classical
  letI : DecidableEq (Fin M) := fun a b => Classical.propDecidable (a = b)
  exact piMass (fun j => rawMass (F.cutoff w j.val.val) (primorial w))

noncomputable def selectedAlignmentRawPivotInsert {M : ℕ} (i : Fin M)
    (x : ({j : Fin M // j ≠ i} → ℕ) × ℤ) : Fin M → ℕ :=
  insertPivotCoordinate i x.1 x.2.toNat

theorem selected_alignment_raw_pivot_expectation {M : ℕ}
    (F : MasterParameterFamily) (w : ℕ) (i : Fin M) (f : (Fin M → ℕ) → ℝ) :
    expectation (conditionalJoint (selectedAlignmentOutsideRawMass F w i)
      (fun _ => integerMass (F.cutoff w i.val) (primorial w)))
      (fun x => f (selectedAlignmentRawPivotInsert i x)) =
    expectation (globalRawMass (F.cutoff w) (primorial w) M) f := by
  classical
  letI : DecidableEq (Fin M) := fun a b => Classical.propDecidable (a = b)
  rw [expectation_conditionalJoint]
  simp only [integerMass, expectation_push, selectedAlignmentRawPivotInsert,
    Int.toNat_natCast]
  simpa only [selectedAlignmentOutsideRawMass, globalRawMass] using
    (expectation_piMass_pivot (fun j : Fin M => rawMass (F.cutoff w j.val) (primorial w)) i f).symm

theorem selected_alignment_raw_pivot_event {M : ℕ}
    (F : MasterParameterFamily) (w : ℕ) (i : Fin M) (P : (Fin M → ℕ) → Prop) :
    event (conditionalJoint (selectedAlignmentOutsideRawMass F w i)
      (fun _ => integerMass (F.cutoff w i.val) (primorial w)))
      (fun x => P (selectedAlignmentRawPivotInsert i x)) =
    event (globalRawMass (F.cutoff w) (primorial w) M) P := by
  classical
  letI : DecidableEq (Fin M) := fun a b => Classical.propDecidable (a = b)
  simp only [event_eq_expectation]
  exact selected_alignment_raw_pivot_expectation F w i (fun x => if P x then 1 else 0)

theorem selected_alignment_outside_raw_geometry
    {d M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (i : Fin M) :
    ∀ᶠ w in atTop, (∀ x, 0 ≤ selectedAlignmentOutsideRawMass F w i x) ∧
      total (selectedAlignmentOutsideRawMass F w i) = 1 := by
  classical
  letI : DecidableEq (Fin M) := fun a b => Classical.propDecidable (a = b)
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  have hz : ∀ j : Fin M, 0 < harmonicNormalizer (F.cutoff w j.val) (primorial w) :=
    fun j => (hw j.val (Finset.mem_range.mpr j.isLt)).2.2
  dsimp only [selectedAlignmentOutsideRawMass]
  exact ⟨piMass_nonneg _ (fun j p => by rw [rawMass_apply]; exact harmonicWeight_nonneg (hz j.val) p),
    piMass_total_one _ (fun j => rawMass_total (hz j.val))⟩

theorem selected_alignment_raw_pivot_support {M : ℕ}
    (F : MasterParameterFamily) (w : ℕ) (i : Fin M)
    (x : ({j : Fin M // j ≠ i} → ℕ) × ℤ)
    (hx : x ∈ (conditionalJoint (selectedAlignmentOutsideRawMass F w i)
      (fun _ => integerMass (F.cutoff w i.val) (primorial w))).support) :
    0 ≤ x.2 ∧ selectedAlignmentRawPivotInsert i x ∈
      (globalRawMass (F.cutoff w) (primorial w) M).support := by
  classical
  letI : DecidableEq (Fin M) := fun a b => Classical.propDecidable (a = b)
  have hn := Finsupp.mem_support_iff.mp hx
  rw [conditionalJoint_apply] at hn
  have hp : x.2 ∈ (integerMass (F.cutoff w i.val) (primorial w)).support :=
    Finsupp.mem_support_iff.mpr (mul_ne_zero_iff.mp hn).2
  obtain ⟨p,hp,hpx⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hp)
  have heq : (p : ℤ) = x.2 := hpx
  have hcoef := congrArg (fun μ => μ (x.1,p))
    (piMass_pivotCoordinate (fun j : Fin M => rawMass (F.cutoff w j.val) (primorial w)) i)
  rw [Finsupp.mapDomain_equiv_apply, tensor_apply] at hcoef
  refine ⟨heq ▸ Int.natCast_nonneg p, ?_⟩
  apply Finsupp.mem_support_iff.mpr
  have hp' : x.2.toNat = p := by rw [← heq]; simp
  change (piMass (fun j : Fin M => rawMass (F.cutoff w j.val) (primorial w)))
    (insertPivotCoordinate i x.1 x.2.toNat) ≠ 0
  rw [hp']
  change (piMass (fun j : Fin M => rawMass (F.cutoff w j.val) (primorial w)))
    ((pivotCoordinateEquiv i).symm (x.1,p)) ≠ 0
  rw [hcoef]
  apply mul_ne_zero _ (Finsupp.mem_support_iff.mp hp)
  simpa only [selectedAlignmentOutsideRawMass] using (mul_ne_zero_iff.mp hn).1

theorem selected_alignment_raw_coordinate_event
    {d M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (i : Fin M) :
    ∀ᶠ w in atTop, ∀ P : ℕ → Prop,
      event (globalRawMass (F.cutoff w) (primorial w) M) (fun x => P (x i)) =
      event (rawMass (F.cutoff w i.val) (primorial w)) P := by
  classical
  letI : DecidableEq (Fin M) := fun a b => Classical.propDecidable (a = b)
  filter_upwards [selected_alignment_outside_raw_geometry hF i] with w hw P
  rw [event_eq_expectation]
  change expectation (piMass (fun j : Fin M => rawMass (F.cutoff w j.val) (primorial w))) _ = _
  rw [expectation_piMass_pivot _ i]
  simp only [insertPivotCoordinate_self]
  rw [expectation_const]
  have ht := hw.2
  dsimp only [selectedAlignmentOutsideRawMass] at ht
  rw [ht, one_mul, ← event_eq_expectation]

end Hindman168
