import Hindman168.SelectedAlignmentKeySourceCompactness
import Hindman168.SelectedAlignmentNativeRouteLimit
import Hindman168.SelectedAlignmentRouteCell
import Hindman168.SelectedAlignmentRoutePrelimitReadings
import Hindman168.SelectedAlignmentFailureCompactness

/-! The local uniform route failure has vanishing ORIGINAL full-raw mass.
The proof extracts from every cofinal positive failure event, keeping the
same actual recipes, source, full anchor and finite factor catalogue. -/
namespace Hindman168
open Filter MeasureTheory FiniteMass Module
open scoped Topology Manifold ContDiff Classical ENNReal NNReal
universe u
attribute [local instance] lieGroup_smooth_min_three alignmentAddingPairFintype

theorem selected_alignment_recipe_route_failure_tendsto
    {d n M s : ℕ} {κ : Type} [Fintype κ]
    {A : Finset ℚ} {Poly : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A Poly F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n)
    (requests : List (AlignmentPivotRequest n i))
    (hown : ∀ request ∈ requests, ∀ word ∈ request.words, ∀ l ∈ word,
      l.1.targetTail = request.tail)
    (incoming : Finset (Fin n → ℚ)) (q₀ : ℕ) (hq : 0 < q₀)
    (hint : ∀ stage ∈ selectedAlignmentCosetPlan (κ := κ) s requests,
      ∀ b ∈ alignmentAllScaleStates i
        (alignmentForwardOptions (selectedAlignmentCosetPlan (κ := κ) s requests)) incoming,
      ∀ l ∈ alignmentWordLetters stage.target.words,
        (q₀ : ℚ) * alignmentLetterScalar b l ∈ (Int.castRingHom ℚ).range)
    (b : Fin n → ℚ) (hb : b ∈ incoming) (hpos : ∀ j, 0 < b j)
    (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ) (θ : ℝ) (hθ : 0 < θ) :
    let plan := selectedAlignmentCosetPlan (κ := κ) s requests
    let catalogue := alignmentJointRouteFactorCatalogue κ q₀ plan incoming requests
    ∀ (D : catalogue → NativeNilmanifoldData.{u} s) (r : catalogue → ℕ)
      (v : ∀ ν, Fin (r ν+1) → AlignmentAddingPair M (principalAlignmentEmbedding e heM i) → ℤ)
      (hv : ∀ ν, Function.Injective (alignmentNativeFiniteEvaluation
        (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (r ν) (v ν)))
      (dim : catalogue → ℕ)
      (basis : ∀ ν, Basis (Fin (dim ν)) ℝ (alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν)).E)
      (obs : ∀ ν, ℕ → (ℤ × ℤ) → C((D ν).G ⧸ (D ν).Γ, ℝ))
      (g a : ∀ ν, ℕ → (ℤ × ℤ) → (D ν).G) (B : catalogue → ℝ) (Lip : catalogue → ℝ≥0),
      (∀ ν w p z, |obs ν w p z| ≤ B ν) →
      (∀ ν w p x y, dist (obs ν w p x) (obs ν w p y) ≤
        (Lip ν : ℝ) * @dist ((D ν).G ⧸ (D ν).Γ) (D ν).metric.toDist x y) →
      (∀ ν, S (ν.val.1.erase i) ν.val.2.1 ν.val.2.2.1 =
        piecewiseLinearNilsequence (D ν).Γ F (fun _ => (⟨energyPadding e i,heM _⟩ : Fin M))
          (obs ν) (g ν) (a ν)) →
      Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) M)
        (fun x => selectedAlignmentRawRouteCellMass F e heM i q₀ w x S θ plan b requests <
          ((3 / (4 * ((principalPivotRoutes plan).card : ℝ≥0)) : ℝ≥0) : ℝ≥0∞))) atTop (𝓝 0) := by
  dsimp only
  intro D r v hv dim basis obs g a B Lip hB hLip hrecipe
  let plan := selectedAlignmentCosetPlan (κ := κ) s requests
  let catalogue := alignmentJointRouteFactorCatalogue κ q₀ plan incoming requests
  let Q := (principalPivotRoutes plan).card
  have hQ : 0 < Q := Finset.card_pos.mpr (selected_alignment_coset_routes_nonempty (κ := κ) s requests)
  have hQR : (0 : ℝ≥0) < Q := by exact_mod_cast hQ
  have hlt : ((3 / (4 * (Q : ℝ≥0)) : ℝ≥0) : ℝ≥0∞) < ((1 / (Q : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
    apply ENNReal.coe_lt_coe.mpr
    apply (div_lt_div_iff₀ (by positivity) hQR).mpr
    nlinarith
  apply selected_alignment_failure_mass_zero_of_compactness
    (fun w => globalRawMass (F.cutoff w) (primorial w) M)
    (fun w x => selectedAlignmentRawRouteCellMass F e heM i q₀ w x S θ plan b requests) _ _ hlt
    ((alignmentGlobalRawMass_geometry hF).mono (fun _ hw => hw.1))
  intro W hW β hβ hbad
  let T : catalogue → Finset (Fin n) := fun ν => ν.val.1.erase i
  let targets := fun ν : catalogue => (T ν).image (principalAlignmentEmbedding e heM)
  let stored : catalogue → AlignmentAddingPair n i → ℤ := fun ν => ν.val.2.2.2
  let V : catalogue → Finset (AlignmentAddingPair n i → ℤ) := fun ν => {stored ν}
  let U : catalogue → Finset (AlignmentAddingPair n i → ℤ) :=
    fun _ => selectedAlignmentRouteQueryCatalogue q₀ plan incoming requests
  let gap : Fin M := ⟨energyPadding e i,heM _⟩
  have hgap : gap ≤ principalAlignmentEmbedding e heM i := (energyPadding_lt_principal e i).le
  have hT : ∀ ν j, j ∈ T ν → j < i := fun ν =>
    selected_alignment_catalogue_factor_tail_before κ q₀ plan incoming requests ν.val ν.property
  have hTargets : ∀ ν j, j ∈ targets ν → j < gap := by
    intro ν j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    exact energyPrincipal_lt_padding e (hT ν k hk)
  let gKey := selectedAlignmentFamilyKeyRecipe F e heM i q₀ 1 T V U stored g
  let aKey := selectedAlignmentFamilyKeyRecipe F e heM i q₀ 1 T V U stored a
  let label := fun w key ν => selectedAlignmentKeyLabel F e heM i q₀ w 1 (T ν) (V ν) (U ν) key (stored ν)
  let shift := fun (_w : ℕ) (_key : SelectedAlignmentShortKey M) ν =>
    selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) (stored ν)
  obtain ⟨sample,hs,f,hf,H,hle,period,hperiod,sigma,hRat,h,hh,limit,hconv,hlocal,halpha,hsym,hweak⟩ :=
    selected_alignment_key_source_compactness D r v hv dim basis hF gap hgap e heM i q₀ hq T hT
      targets hTargets 1 V U shift gKey aKey label obs B Lip hB hLip W hW
      (fun m x => selectedAlignmentRawRouteCellMass F e heM i q₀ (W m) x S θ plan b requests <
        ((3 / (4 * (Q : ℝ≥0)) : ℝ≥0) : ℝ≥0∞)) hβ hbad
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))
  letI : MeasurableSpace J.G := borel J.G
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (J.G ⧸ J.Γ) := native_nilmanifold_metric_coset_borel J
  let key := fun m ν => selectedAlignmentSourceKey F e heM i (W (f m)) (T ν) (sample (f m))
  let obs_m := fun m ν => obs ν (W (f m)) (label (W (f m)) (key m ν) ν)
  let L := fun m => (selectedPrincipalMicrocellLength F e (W (f m)) i : ℝ)
  let P := fun m => alignmentOriginalJointRealSource D r v hv F q₀ (W (f m)) targets (sample (f m))
    (alignmentMicrocellFirst (selectedPrincipalMicrocellWidth F e (W (f m)) i)
      (F.modulus (W (f m))) (sample (f m) (principalAlignmentEmbedding e heM i)))
    (fun ν => selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) (stored ν))
    (fun ν => gKey (W (f m)) (key m ν) ν) (fun ν => aKey (W (f m)) (key m ν) ν)
  have hL : Tendsto L atTop atTop := (selected_principal_microcell_length_tendsto hF e i).comp (hW.comp hf.tendsto_atTop)
  have hlocal' : NativeResidueLocalHaarLaw J H L P period hperiod sigma hRat h := by
    convert hlocal using 1
    · funext m
      exact congrArg (fun a : ℕ => (a : ℝ))
        (alignmentGeometryWithGap_localLength F e i (principalAlignmentEmbedding e heM i) rfl (W (f m))).symm
    · funext m t
      simp only [alignmentGeometryWithGap_gap]
      rfl
  have hsym' : ∀ z β, SelectedAlignmentCatalogueCosetSymmetry D r v hv targets gap.val H
      (sigma z) (hRat z) (h β) := by
    intro z β
    have hz : signedPeriodResidue period hperiod (z.val : ℤ) = z := by
      apply Fin.ext
      simp only [signedPeriodResidue]
      rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast z.isLt)]
      simp
    simpa only [hz] using hsym β (z.val : ℤ)
  let factor := alignmentJointFiniteFactorLookup catalogue
  have hfactor : ∀ route ∈ principalPivotRoutes plan,
      ∀ request ∈ requests, ∀ c₀ ∈ request.leading, ∀ word ∈ request.words, ∀ c,
      let arithmetic := alignmentJointRouteArithmetic q₀ plan b route
      let st := arithmetic.2.toAdd + alignmentAuxiliaryWord q₀ arithmetic.1 word
      ∃ ν, factor (insert i request.tail) (c₀*finiteScaleBlockProduct arithmetic.1 (insert i request.tail)) c st = some ν ∧
        ∀ l ∈ word, targets ν = l.1.targetTail.image (principalAlignmentEmbedding e heM) := by
    intro route hr request hreq c₀ hc word hw c
    let ar := alignmentJointRouteArithmetic q₀ plan b route
    have hm := alignment_joint_route_terminal_factor_mem κ q₀ plan incoming requests b hb route hr request hreq c₀ hc word hw c
    let ν : catalogue := ⟨_,hm⟩
    refine ⟨ν,alignment_joint_finite_factor_lookup_mem _ _ _ _ _ hm,?_⟩
    intro l hl
    change ((insert i request.tail).erase i).image _ = _
    rw [alignment_request_factor_target, hown request hreq word hw l hl]
  have hlim := selected_alignment_native_route_empirical_liminf (principalAlignmentEmbedding e heM) i
    D r v hv targets gap.val (fun p => selected_alignment_mapped_letter_before_padding e heM p)
    H period hperiod sigma hRat h hh.continuous hsym' factor limit obs_m hconv L hL P hlocal'
    requests incoming q₀ hint b hb hpos θ hθ hfactor
  let read_m := fun m => selectedAlignmentJointRouteNativeReading (principalAlignmentEmbedding e heM) i
    D r v hv factor (fun ν => obs_m m ν)
  have hevent : ∀ᶠ m in atTop,
      (finiteEmpiricalProbability (Finset.Ico 0 ⌊L m⌋)
        (fun z => (P m (z:ℝ) : J.G ⧸ J.Γ)) (1:J.G) : Measure (J.G ⧸ J.Γ))
        (selectedAlignmentRouteActualSet (read_m m) θ q₀ plan b requests (principalPivotRoutes plan)) =
      selectedAlignmentRawRouteCellMass F e heM i q₀ (W (f m)) (sample (f m)) S θ plan b requests := by
    filter_upwards [hf.tendsto_atTop.eventually hs, hL.eventually_ge_atTop 1] with m hm hl
    have hlen : 0 < selectedPrincipalMicrocellLength F e (W (f m)) i := by
      exact_mod_cast (show (0:ℝ) < selectedPrincipalMicrocellLength F e (W (f m)) i by linarith)
    simp only [L, Int.floor_natCast, selectedAlignmentRawRouteCellMass, selectedAlignmentRawCellProbability]
    apply selected_alignment_empirical_event_congr _ (Finset.nonempty_Ico.mpr (by exact_mod_cast hlen))
    · letI : TopologicalSpace (J.G ⧸ J.Γ) := QuotientGroup.instTopologicalSpace J.Γ
      letI : BorelSpace (J.G ⧸ J.Γ) := native_nilmanifold_coset_borel J
      exact selected_alignment_route_actual_measurable (read_m m)
        (fun B a c st qu => selected_alignment_joint_route_native_reading_continuous
          (principalAlignmentEmbedding e heM) i D r v hv factor (fun ν => obs_m m ν)
          (fun ν => (obs_m m ν).continuous) B a c st qu) θ q₀ plan b requests _
    · exact Set.to_countable _ |>.measurableSet
    · intro ell hell
      have hh' := selected_alignment_catalogue_key_route_microcell e heM i catalogue D r v hv F q₀
        (W (f m)) 1 V U (sample (f m)) obs g a (fun ν => Finset.mem_singleton_self _)
        hm.1 hm.2.2 S hrecipe plan incoming requests b hb (Finset.Subset.refl _) (fun _ => Finset.Subset.refl _)
        θ (by omega) ell hell
      simpa only [selectedAlignmentCatalogueKeyPoint, selectedAlignmentCatalogueKeyReading,
        P, read_m, obs_m, key, shift, gKey, aKey, label, T, stored, factor,
        selectedAlignmentFamilyKeyRecipe, selectedAlignmentKeyRecipe,
        alignment_original_joint_real_source_integer] using hh'
  refine ⟨f,hf,(fun m => sample (f m)),?_,?_⟩
  · exact (hf.tendsto_atTop.eventually hs).mono (fun _ hm => hm.2.1)
  · calc
      _ ≤ _ := hlim
      _ = _ := liminf_congr hevent

end Hindman168
