import Hindman168.SelectedAlignmentRouteCell
import Hindman168.SelectedAlignmentRouteNumericalPivot
import Hindman168.PositivePrincipalSumHarmonicCellTransfer
import Hindman168.AlignmentJointRouteReadingsCatalogue

/-! The actual local route mass is constant on the original earlier-data
and microcell/residue fibers. Later raw coordinates remain arbitrary.
Only blocks coming from genuine requests use the request.before property. -/
namespace Hindman168
open scoped Classical

theorem selected_alignment_microcell_first_eq (R modulus : ℕ) (p q : ℤ)
    (hpq : principalMicrocellExposure R modulus p = principalMicrocellExposure R modulus q) :
    alignmentMicrocellFirst R modulus p = alignmentMicrocellFirst R modulus q := by
  have hd : p / (R:ℤ) = q / (R:ℤ) := congrArg Prod.fst hpq
  have hr : p % (modulus:ℤ) = q % (modulus:ℤ) := congrArg Prod.snd hpq
  unfold alignmentMicrocellFirst alignmentResidueEndpoint
  rw [hd]
  congr 1
  exact (show Int.ModEq (modulus:ℤ) p q from hr).sub_right _

theorem selected_alignment_raw_reading_earlier_eq {n M : ℕ} {κ : Type*}
    (f : Fin n ↪o Fin M) (i : Fin n) (F : MasterParameterFamily) (q₀ w : ℕ)
    (x y : Fin M → ℕ) (hxy : ∀ j < f i, x j = y j)
    (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ)
    (B : Finset (Fin n)) (hB : ∀ j ∈ B.erase i, j < i)
    (a : ℚ) (c : κ) (stored query : AlignmentAddingPair n i → ℤ) (p : ℤ) :
    selectedAlignmentRouteRawReading f i F q₀ w x S B a c stored query p =
      selectedAlignmentRouteRawReading f i F q₀ w y S B a c stored query p := by
  have hT : ∀ j ∈ (B.erase i).image f, j < f i := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    exact f.strictMono (hB k hk)
  have hρ : (fun e : AlignmentAddingPair M (f i) => alignmentPairResidue q₀ w (F.modulus w) e x) =
      (fun e => alignmentPairResidue q₀ w (F.modulus w) e y) :=
    funext (alignment_residue_eq_of_earlier_eq hxy q₀ w (F.modulus w))
  have hΔ : (fun e : AlignmentAddingPair M (f i) => alignmentPairProgression q₀ w (F.modulus w) e x) =
      (fun e => alignmentPairProgression q₀ w (F.modulus w) e y) :=
    funext (alignment_progression_eq_of_earlier_eq hxy q₀ w (F.modulus w))
  simp only [selectedAlignmentRouteRawReading, alignmentIntegerArrayArgument,
    alignment_block_product_eq_of_earlier_eq hxy _ hT, hρ, hΔ]

/-- The event uses only genuine request blocks. No restriction is imposed
on the observer's values on arbitrary other blocks. -/
theorem selected_alignment_raw_route_set_earlier_eq {n M : ℕ} {κ : Type*}
    (f : Fin n ↪o Fin M) (i : Fin n) (F : MasterParameterFamily) (q₀ w : ℕ)
    (x y : Fin M → ℕ) (hxy : ∀ j < f i, x j = y j)
    (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ)
    (θ : ℝ) (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i))
    (routes : Finset (List (ℕ × List (AlignmentAddingPair n i × ℚ)))) :
    selectedAlignmentRouteActualSet (selectedAlignmentRouteRawReading f i F q₀ w x S)
      θ q₀ plan b requests routes =
    selectedAlignmentRouteActualSet (selectedAlignmentRouteRawReading f i F q₀ w y S)
      θ q₀ plan b requests routes := by
  have hread (request : AlignmentPivotRequest n i) (a : ℚ) (c : κ)
      (stored query : AlignmentAddingPair n i → ℤ) (p : ℤ) :
      selectedAlignmentRouteRawReading f i F q₀ w x S (insert i request.tail) a c stored query p =
      selectedAlignmentRouteRawReading f i F q₀ w y S (insert i request.tail) a c stored query p := by
    apply selected_alignment_raw_reading_earlier_eq f i F q₀ w x y hxy S
    simpa only [alignment_request_factor_target] using request.before
  ext p
  constructor
  · rintro ⟨route,hr,hreq⟩
    refine ⟨route,hr,?_⟩
    dsimp only at hreq ⊢
    intro request hrequest a ha word hw c
    simpa only [hread] using hreq request hrequest a ha word hw c
  · rintro ⟨route,hr,hreq⟩
    refine ⟨route,hr,?_⟩
    dsimp only at hreq ⊢
    intro request hrequest a ha word hw c
    simpa only [hread] using hreq request hrequest a ha word hw c

theorem selected_alignment_raw_cell_probability_eq {n M : ℕ}
    (F : MasterParameterFamily) (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (i : Fin n) (w : ℕ) (x y : Fin M → ℕ)
    (hcell : principalMicrocellExposure (selectedPrincipalMicrocellWidth F e w i) (F.modulus w)
      (x (principalAlignmentEmbedding e heM i)) =
      principalMicrocellExposure (selectedPrincipalMicrocellWidth F e w i) (F.modulus w)
      (y (principalAlignmentEmbedding e heM i))) :
    selectedAlignmentRawCellProbability F e heM i w x =
      selectedAlignmentRawCellProbability F e heM i w y := by
  simp only [selectedAlignmentRawCellProbability, selected_alignment_microcell_first_eq _ _ _ _ hcell]

/-- Literal equality of the conditional local mass, valid without support,
master growth, or positive window length hypotheses (including the fallback). -/
theorem selected_alignment_raw_route_cell_mass_invariant {n M : ℕ} {κ : Type*}
    (F : MasterParameterFamily) (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (i : Fin n) (q₀ w : ℕ) (x y : Fin M → ℕ)
    (hxy : ∀ j < principalAlignmentEmbedding e heM i, x j = y j)
    (hcell : principalMicrocellExposure (selectedPrincipalMicrocellWidth F e w i) (F.modulus w)
      (x (principalAlignmentEmbedding e heM i)) =
      principalMicrocellExposure (selectedPrincipalMicrocellWidth F e w i) (F.modulus w)
      (y (principalAlignmentEmbedding e heM i)))
    (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ) (θ : ℝ)
    (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i)) :
    selectedAlignmentRawRouteCellMass F e heM i q₀ w x S θ plan b requests =
      selectedAlignmentRawRouteCellMass F e heM i q₀ w y S θ plan b requests := by
  unfold selectedAlignmentRawRouteCellMass
  rw [selected_alignment_raw_cell_probability_eq F e heM i w x y hcell,
    selected_alignment_raw_route_set_earlier_eq (principalAlignmentEmbedding e heM)
      i F q₀ w x y hxy S θ plan b requests]

end Hindman168
