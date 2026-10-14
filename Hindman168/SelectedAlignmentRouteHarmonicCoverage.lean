import Hindman168.SelectedAlignmentRouteFineGood
import Hindman168.PositivePrincipalSumHarmonicCellSelected

/-! The actual uniform route event transfers to the original harmonic
microcell kernel, then to signed secured thresholds with the actual shifts.
The likelihood loss is paid once for the union, not once per route. -/
namespace Hindman168
open Filter FiniteMass MeasureTheory
open scoped Classical Topology ENNReal NNReal BigOperators
attribute [local instance] alignmentAddingPairFintype

theorem selected_alignment_good_fine_harmonic_cover
    {d n M : ℕ} {κ : Type*} {A : Finset ℚ} {Poly : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A Poly F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n) (q₀ : ℕ)
    (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ) (θ : ℝ)
    (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i)) (hQ : 0 < (principalPivotRoutes plan).card) :
    ∀ᶠ w in atTop,
      ∀ outside : {j : Fin M // j ≠ principalAlignmentEmbedding e heM i} → ℕ,
      ∀ t ∈ ((integerMass (F.cutoff w (energyPrincipal e i)) (primorial w)).mapDomain
        (principalMicrocellExposure (selectedPrincipalMicrocellWidth F e w i) (F.modulus w))).support,
      selectedAlignmentFineRouteGood F e heM i q₀ w S θ plan b requests outside t →
      1 / (2 * ((principalPivotRoutes plan).card : ℝ)) ≤
        ∑ route : principalPivotRoutes plan,
          event (conditionMass (integerMass (F.cutoff w (energyPrincipal e i)) (primorial w))
            (fun z => principalMicrocellExposure (selectedPrincipalMicrocellWidth F e w i) (F.modulus w) z = t))
          (fun z => selectedAlignmentSignedRouteSecured (principalAlignmentEmbedding e heM) i F q₀ w
            (insertPivotCoordinate (principalAlignmentEmbedding e heM i) outside 0) S θ plan b requests
            (z + selectedAlignmentOutsideRouteShift (principalAlignmentEmbedding e heM) i F q₀ w plan b route.val outside)) := by
  have hlen := (selected_principal_microcell_length_tendsto hF e i).eventually_ge_atTop 1
  filter_upwards [principal_selected_microcell_cover_transfer hF e heM i
    (V := principalPivotRoutes plan) (principalPivotRoutes plan).card hQ, hlen]
    with w hw hl outside t ht hg
  obtain ⟨z,hz,hzt⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ht)
  obtain ⟨p,hp,hpz⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hz)
  have hpt : principalMicrocellExposure (selectedPrincipalMicrocellWidth F e w i) (F.modulus w) (p : ℤ) = t := by
    simpa only [hpz] using hzt
  have hc := (hg p hpt).1
  have hm := (hg p hpt).2
  have hcp : p.Coprime (primorial w) := (Finset.mem_filter.mp (rawMass_support_window _ _ hp)).2
  have hposlen : 0 < selectedPrincipalMicrocellLength F e w i := by
    exact_mod_cast (show (0:ℝ) < selectedPrincipalMicrocellLength F e w i by linarith)
  let x := insertPivotCoordinate (principalAlignmentEmbedding e heM i) outside p
  let P := fun (route : principalPivotRoutes plan) z =>
    selectedAlignmentSignedRouteSecured (principalAlignmentEmbedding e heM) i F q₀ w
      (insertPivotCoordinate (principalAlignmentEmbedding e heM i) outside 0) S θ plan b requests
      (z + selectedAlignmentOutsideRouteShift (principalAlignmentEmbedding e heM) i F q₀ w plan b route.val outside)
  have hcover : 3 / (4 * ((principalPivotRoutes plan).card : ℝ)) ≤
      event (uniformIntervalMass 0 (selectedPrincipalMicrocellLength F e w i))
        (fun ell => ∃ route, P route (alignmentMicrocellFirst
          (selectedPrincipalMicrocellWidth F e w i) (F.modulus w) p + (F.modulus w : ℤ)*ell)) := by
    have hm' := ENNReal.toReal_mono (show selectedAlignmentRawRouteCellMass F e heM i q₀ w x S θ plan b requests ≠ ∞ from
      measure_ne_top _ _) hm
    simp only [ENNReal.coe_toReal, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
      NNReal.coe_ofNat] at hm'
    rw [selectedAlignmentRawRouteCellMass, selected_alignment_raw_cell_event_toReal F e heM i w x hposlen] at hm'
    apply hm'.trans
    apply event_mono _ (uniformIntervalMass_nonneg _ _)
    intro ell hell
    simpa only [x, insertPivotCoordinate_self, P] using
      selected_alignment_raw_route_yields_outside_secured (principalAlignmentEmbedding e heM) i F q₀ w outside p
        S θ plan b requests _ hell
  have hh := hw p hcp hc.1 hc.2 P hcover
  simpa only [P, hpt] using hh

end Hindman168
