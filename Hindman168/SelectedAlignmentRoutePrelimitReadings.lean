import Hindman168.SelectedAlignmentSourceKeyRecipeFamily
import Hindman168.SelectedAlignmentRouteNumerical
import Hindman168.AlignmentJointRouteReadingsCatalogue
import Hindman168.AlignmentMicrocellFirst

/-! Exact prelimit readings on the original selected microcell. The finite
factor subtype fixes its target and stored slot before source selection.
Every equality uses the original padding recipe and the same joint orbit. -/
namespace Hindman168
open FiniteMass
open scoped Classical Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three alignmentAddingPairFintype

/-- All queries needed by the actual finite route options, including the
center query. This catalogue does not depend on a source or a chosen lift. -/
noncomputable def selectedAlignmentRouteQueryCatalogue {n : ℕ} {i : Fin n}
    (q₀ : ℕ) (plan : List (AlignmentPivotStage n i))
    (incoming : Finset (Fin n → ℚ)) (requests : List (AlignmentPivotRequest n i)) :
    Finset (AlignmentAddingPair n i → ℤ) :=
  {0} ∪ incoming.biUnion (fun b => (principalPivotRoutes plan).biUnion (fun route =>
    requests.toFinset.biUnion (fun request => request.words.image (fun word =>
      alignmentAuxiliaryWord q₀ (alignmentJointRouteArithmetic q₀ plan b route).1 word))))

theorem selected_alignment_route_query_zero {n : ℕ} {i : Fin n}
    (q₀ : ℕ) (plan : List (AlignmentPivotStage n i))
    (incoming : Finset (Fin n → ℚ)) (requests : List (AlignmentPivotRequest n i)) :
    0 ∈ selectedAlignmentRouteQueryCatalogue q₀ plan incoming requests :=
  Finset.mem_union_left _ (Finset.mem_singleton_self _)

theorem selected_alignment_route_query_mem {n : ℕ} {i : Fin n}
    (q₀ : ℕ) (plan : List (AlignmentPivotStage n i))
    (incoming : Finset (Fin n → ℚ)) (requests : List (AlignmentPivotRequest n i))
    (b : Fin n → ℚ) (hb : b ∈ incoming)
    (route : List (ℕ × List (AlignmentAddingPair n i × ℚ))) (hr : route ∈ principalPivotRoutes plan)
    (request : AlignmentPivotRequest n i) (hrequest : request ∈ requests)
    (word : List (AlignmentAddingPair n i × ℚ)) (hw : word ∈ request.words) :
    alignmentAuxiliaryWord q₀ (alignmentJointRouteArithmetic q₀ plan b route).1 word ∈
      selectedAlignmentRouteQueryCatalogue q₀ plan incoming requests :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b,hb,Finset.mem_biUnion.mpr ⟨route,hr,
    Finset.mem_biUnion.mpr ⟨request,List.mem_toFinset.mpr hrequest,
      Finset.mem_image.mpr ⟨word,hw,rfl⟩⟩⟩⟩)

/-- Every stored factor in the actual route catalogue has an earlier tail,
including terminal factors with the shifted stored slot. -/
theorem selected_alignment_catalogue_factor_tail_before {n : ℕ} {i : Fin n}
    (κ : Type) [Fintype κ] (q₀ : ℕ) (plan : List (AlignmentPivotStage n i))
    (incoming : Finset (Fin n → ℚ)) (requests : List (AlignmentPivotRequest n i))
    (factor : AlignmentJointRouteFactor i κ)
    (hfactor : factor ∈ alignmentJointRouteFactorCatalogue κ q₀ plan incoming requests) :
    ∀ j ∈ factor.1.erase i, j < i := by
  letI : DecidableEq (AlignmentAddingPair n i → ℤ) := Classical.decEq _
  obtain ⟨b,hb,hfactor⟩ := Finset.mem_biUnion.mp hfactor
  obtain ⟨route,hr,hfactor⟩ := Finset.mem_biUnion.mp hfactor
  obtain ⟨request,hrequest,hfactor⟩ := Finset.mem_biUnion.mp hfactor
  obtain ⟨a,ha,hfactor⟩ := Finset.mem_biUnion.mp hfactor
  obtain ⟨c,hc,hfactor⟩ := Finset.mem_biUnion.mp hfactor
  rcases Finset.mem_union.mp hfactor with hcenter | hterminal
  · obtain rfl := Finset.mem_singleton.mp hcenter
    simpa only [alignment_request_factor_target] using request.before
  · obtain ⟨word,hw,rfl⟩ := Finset.mem_image.mp hterminal
    simpa only [alignment_request_factor_target] using request.before

/-- Every point of the actual selected microcell stays within one padding
microcell width of its anchor. The length is the original integer length. -/
theorem selected_alignment_microcell_point_distance {n : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (w : ℕ) (i : Fin n) (p ell : ℤ)
    (hell : ell ∈ Finset.Ico 0 (selectedPrincipalMicrocellLength F e w i : ℤ)) :
    |alignmentMicrocellFirst (selectedPrincipalMicrocellWidth F e w i)
      (F.modulus w) p + (F.modulus w : ℤ)*ell - p| ≤
      (selectedPrincipalMicrocellWidth F e w i : ℤ) := by
  have hm : (0 : ℤ) < (F.modulus w : ℕ) := by exact_mod_cast (F.modulus w).pos
  have hl := Finset.mem_Ico.mp hell
  have hlen : (0 : ℤ) < selectedPrincipalMicrocellLength F e w i := lt_of_le_of_lt hl.1 hl.2
  have he : (F.modulus w : ℤ) * (selectedPrincipalMicrocellLength F e w i : ℤ) =
      (selectedPrincipalMicrocellWidth F e w i : ℤ) := by
    exact_mod_cast selected_principal_microcell_exact F e w i
  have hR : (0 : ℤ) < selectedPrincipalMicrocellWidth F e w i := by nlinarith
  have hp := Int.ediv_mul_le p hR.ne'
  have hp' := Int.lt_ediv_add_one_mul_self p hR
  have hh := (alignment_residue_progression_interval
    ((p / (selectedPrincipalMicrocellWidth F e w i : ℤ)) * (selectedPrincipalMicrocellWidth F e w i : ℤ))
    (F.modulus w) (selectedPrincipalMicrocellLength F e w i) p ell hm).mpr hl
  change _ ≤ alignmentMicrocellFirst _ _ p + _ ∧ alignmentMicrocellFirst _ _ p + _ < _ at hh
  rw [he] at hh
  rw [abs_le]
  constructor <;> nlinarith [hh.1,hh.2]

section Catalogue
variable {n M s : ℕ} {κ : Type} (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n)
  (catalogue : Finset (AlignmentJointRouteFactor i κ))
  (D : catalogue → NativeNilmanifoldData.{u} s) (r : catalogue → ℕ)
  (v : ∀ ν, Fin (r ν+1) → AlignmentAddingPair M (principalAlignmentEmbedding e heM i) → ℤ)
  (hv : ∀ ν, Function.Injective (alignmentNativeFiniteEvaluation
    (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (r ν) (v ν)))
  (F : MasterParameterFamily) (q₀ w C : ℕ)
  (V U : catalogue → Finset (AlignmentAddingPair n i → ℤ))
  (x : Fin M → ℕ)
  (obs : ∀ ν, ℕ → (ℤ × ℤ) → C((D ν).G ⧸ (D ν).Γ, ℝ))
  (g a : ∀ ν, ℕ → (ℤ × ℤ) → (D ν).G)

noncomputable def selectedAlignmentCatalogueKeyPoint (p ell : ℤ) :
    (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).Γ :=
  QuotientGroup.mk (alignmentOriginalJointPointOrbit D r v hv F q₀ w
    (fun ν => (ν.val.1.erase i).image (principalAlignmentEmbedding e heM)) x p
    (fun ν => selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) ν.val.2.2.2)
    (fun ν => selectedAlignmentFamilyKeyRecipe F e heM i q₀ C
      (fun ν => ν.val.1.erase i) V U (fun ν => ν.val.2.2.2) g w
      (selectedAlignmentSourceKey F e heM i w (ν.val.1.erase i) x) ν)
    (fun ν => selectedAlignmentFamilyKeyRecipe F e heM i q₀ C
      (fun ν => ν.val.1.erase i) V U (fun ν => ν.val.2.2.2) a w
      (selectedAlignmentSourceKey F e heM i w (ν.val.1.erase i) x) ν) ell)

noncomputable def selectedAlignmentCatalogueKeyReading :=
  selectedAlignmentJointRouteNativeReading (principalAlignmentEmbedding e heM) i D r v hv
    (alignmentJointFiniteFactorLookup catalogue)
    (fun ν => selectedAlignmentFamilyKeyRecipe F e heM i q₀ C
      (fun ν => ν.val.1.erase i) V U (fun ν => ν.val.2.2.2) obs w
      (selectedAlignmentSourceKey F e heM i w (ν.val.1.erase i) x) ν)

theorem selected_alignment_catalogue_key_reading_eq_raw
    (hzero : ∀ ν, 0 ∈ U ν) (hstored : ∀ ν, ν.val.2.2.2 ∈ V ν)
    (hxs : x ∈ (globalRawMass (F.cutoff w) (primorial w) M).support)
    (hgood : ∀ ν, selectedAlignmentFullExposureArrayStable F e heM i q₀ w C
      (ν.val.1.erase i) (V ν) (U ν) x)
    (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ)
    (hrecipe : ∀ ν, S (ν.val.1.erase i) ν.val.2.1 ν.val.2.2.1 =
      piecewiseLinearNilsequence (D ν).Γ F (fun _ => (⟨energyPadding e i,heM _⟩ : Fin M))
        (obs ν) (g ν) (a ν))
    (B : Finset (Fin n)) (b : ℚ) (c : κ) (stored query : AlignmentAddingPair n i → ℤ)
    (hmem : (B,b,c,stored) ∈ catalogue) (hquery : query ∈ U ⟨(B,b,c,stored),hmem⟩)
    (p ell : ℤ) (hp : Int.ModEq (F.modulus w:ℕ) p (x (principalAlignmentEmbedding e heM i)))
    (hdist : |p+(F.modulus w:ℤ)*ell-x (principalAlignmentEmbedding e heM i)| ≤
      (C*selectedPrincipalMicrocellWidth F e w i:ℕ)) :
    selectedAlignmentCatalogueKeyReading e heM i catalogue D r v hv F q₀ w C V U x obs B b c stored query
      (selectedAlignmentCatalogueKeyPoint e heM i catalogue D r v hv F q₀ w C V U x g a p ell) =
    selectedAlignmentRouteRawReading (principalAlignmentEmbedding e heM) i F q₀ w x S
      B b c stored query (p+(F.modulus w:ℤ)*ell) := by
  let ν : catalogue := ⟨(B,b,c,stored),hmem⟩
  have hh := selected_alignment_key_recipe_native_joint_reading e heM i D r v hv F q₀ w C
    (fun ν => ν.val.1.erase i) ν V U hzero x x hxs
    (alignmentGlobalRawMass_support_coprime F w x hxs)
    (fun k _ => selected_alignment_full_raw_support_cutoff F w x hxs
      (principalAlignmentEmbedding e heM k)) rfl hgood
    (fun ν => ν.val.2.2.2) hstored query hquery p ell hp hdist obs g a
  dsimp only at hh
  unfold selectedAlignmentCatalogueKeyReading selectedAlignmentJointRouteNativeReading
  rw [alignment_joint_finite_factor_lookup_mem catalogue B b c stored hmem]
  change _ = S (B.erase i) b c w _
  rw [hrecipe ν]
  exact hh.symm

theorem selected_alignment_catalogue_key_reading_microcell
    (hzero : ∀ ν, 0 ∈ U ν) (hstored : ∀ ν, ν.val.2.2.2 ∈ V ν)
    (hxs : x ∈ (globalRawMass (F.cutoff w) (primorial w) M).support)
    (hgood : ∀ ν, selectedAlignmentFullExposureArrayStable F e heM i q₀ w C
      (ν.val.1.erase i) (V ν) (U ν) x)
    (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ)
    (hrecipe : ∀ ν, S (ν.val.1.erase i) ν.val.2.1 ν.val.2.2.1 =
      piecewiseLinearNilsequence (D ν).Γ F (fun _ => (⟨energyPadding e i,heM _⟩ : Fin M))
        (obs ν) (g ν) (a ν))
    (B : Finset (Fin n)) (b : ℚ) (c : κ) (stored query : AlignmentAddingPair n i → ℤ)
    (hmem : (B,b,c,stored) ∈ catalogue) (hquery : query ∈ U ⟨(B,b,c,stored),hmem⟩)
    (hC : 1 ≤ C) (ell : ℤ)
    (hell : ell ∈ Finset.Ico 0 (selectedPrincipalMicrocellLength F e w i : ℤ)) :
    selectedAlignmentCatalogueKeyReading e heM i catalogue D r v hv F q₀ w C V U x obs B b c stored query
      (selectedAlignmentCatalogueKeyPoint e heM i catalogue D r v hv F q₀ w C V U x g a (alignmentMicrocellFirst (selectedPrincipalMicrocellWidth F e w i) (F.modulus w) (x (principalAlignmentEmbedding e heM i))) ell) =
    selectedAlignmentRouteRawReading (principalAlignmentEmbedding e heM) i F q₀ w x S
      B b c stored query ((alignmentMicrocellFirst (selectedPrincipalMicrocellWidth F e w i) (F.modulus w) (x (principalAlignmentEmbedding e heM i)))+(F.modulus w:ℤ)*ell) := by
  apply selected_alignment_catalogue_key_reading_eq_raw e heM i catalogue D r v hv F q₀ w C V U
    x obs g a hzero hstored hxs hgood S hrecipe B b c stored query hmem hquery
  · exact alignmentMicrocellFirst_modEq _ _ _
  · exact (selected_alignment_microcell_point_distance F e w i
      (x (principalAlignmentEmbedding e heM i)) ell hell).trans (by
        exact_mod_cast (show selectedPrincipalMicrocellWidth F e w i ≤ C *
          selectedPrincipalMicrocellWidth F e w i by nlinarith))

end Catalogue

/-- Exact finite-catalogue equality identifies the full route success event.
The center and terminal membership proofs are the actual route catalogues. -/
theorem selected_alignment_route_actual_pullback
    {n : ℕ} {i : Fin n} {κ : Type} {X Y : Type*} [Fintype κ]
    (read : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) →
      (AlignmentAddingPair n i → ℤ) → X → ℝ)
    (raw : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) →
      (AlignmentAddingPair n i → ℤ) → Y → ℝ)
    (q₀ : ℕ) (plan : List (AlignmentPivotStage n i))
    (incoming : Finset (Fin n → ℚ)) (requests : List (AlignmentPivotRequest n i))
    (b : Fin n → ℚ) (hb : b ∈ incoming) (x : X) (y : Y)
    (heq : ∀ B a c stored, (B,a,c,stored) ∈
      alignmentJointRouteFactorCatalogue κ q₀ plan incoming requests →
      ∀ query ∈ selectedAlignmentRouteQueryCatalogue q₀ plan incoming requests,
      read B a c stored query x = raw B a c stored query y)
    (θ : ℝ) :
    x ∈ selectedAlignmentRouteActualSet read θ q₀ plan b requests (principalPivotRoutes plan) ↔
    y ∈ selectedAlignmentRouteActualSet raw θ q₀ plan b requests (principalPivotRoutes plan) := by
  have hcmp : ∀ route ∈ principalPivotRoutes plan, ∀ request ∈ requests,
      ∀ a ∈ request.leading, ∀ word ∈ request.words, ∀ c : κ,
      let ar := alignmentJointRouteArithmetic q₀ plan b route
      let B := insert i request.tail
      let lead := a * finiteScaleBlockProduct ar.1 B
      (2*θ < read B lead c ar.2.toAdd 0 x →
        θ < read B lead c (ar.2.toAdd+alignmentAuxiliaryWord q₀ ar.1 word)
          (alignmentAuxiliaryWord q₀ ar.1 word) x) ↔
      (2*θ < raw B lead c ar.2.toAdd 0 y →
        θ < raw B lead c (ar.2.toAdd+alignmentAuxiliaryWord q₀ ar.1 word)
          (alignmentAuxiliaryWord q₀ ar.1 word) y) := by
    intro route hr request hrequest a ha word hw c
    dsimp only
    rw [heq _ _ _ _ (alignment_joint_route_center_factor_mem κ q₀ plan incoming requests
      b hb route hr request hrequest a ha c) _
      (selected_alignment_route_query_zero q₀ plan incoming requests),
      heq _ _ _ _ (alignment_joint_route_terminal_factor_mem κ q₀ plan incoming requests
      b hb route hr request hrequest a ha word hw c) _
      (selected_alignment_route_query_mem q₀ plan incoming requests b hb route hr request hrequest word hw)]
  constructor
  · rintro ⟨route,hr,h⟩
    exact ⟨route,hr,fun request hrequest a ha word hw c =>
      (hcmp route hr request hrequest a ha word hw c).mp (h request hrequest a ha word hw c)⟩
  · rintro ⟨route,hr,h⟩
    exact ⟨route,hr,fun request hrequest a ha word hw c =>
      (hcmp route hr request hrequest a ha word hw c).mpr (h request hrequest a ha word hw c)⟩

section Route
variable {n M s : ℕ} {κ : Type} (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n)
  (catalogue : Finset (AlignmentJointRouteFactor i κ))
  (D : catalogue → NativeNilmanifoldData.{u} s) (r : catalogue → ℕ)
  (v : ∀ ν, Fin (r ν+1) → AlignmentAddingPair M (principalAlignmentEmbedding e heM i) → ℤ)
  (hv : ∀ ν, Function.Injective (alignmentNativeFiniteEvaluation
    (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (r ν) (v ν)))
  (F : MasterParameterFamily) (q₀ w C : ℕ)
  (V U : catalogue → Finset (AlignmentAddingPair n i → ℤ))
  (x : Fin M → ℕ)
  (obs : ∀ ν, ℕ → (ℤ × ℤ) → C((D ν).G ⧸ (D ν).Γ, ℝ))
  (g a : ∀ ν, ℕ → (ℤ × ℤ) → (D ν).G)


theorem selected_alignment_catalogue_key_route_microcell
    [Fintype κ] (hstored : ∀ ν, ν.val.2.2.2 ∈ V ν)
    (hxs : x ∈ (globalRawMass (F.cutoff w) (primorial w) M).support)
    (hgood : ∀ ν, selectedAlignmentFullExposureArrayStable F e heM i q₀ w C
      (ν.val.1.erase i) (V ν) (U ν) x)
    (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ)
    (hrecipe : ∀ ν, S (ν.val.1.erase i) ν.val.2.1 ν.val.2.2.1 =
      piecewiseLinearNilsequence (D ν).Γ F (fun _ => (⟨energyPadding e i,heM _⟩ : Fin M))
        (obs ν) (g ν) (a ν))
    (plan : List (AlignmentPivotStage n i)) (incoming : Finset (Fin n → ℚ))
    (requests : List (AlignmentPivotRequest n i)) (b : Fin n → ℚ) (hb : b ∈ incoming)
    (hcatalogue : alignmentJointRouteFactorCatalogue κ q₀ plan incoming requests ⊆ catalogue)
    (hqueries : ∀ ν, selectedAlignmentRouteQueryCatalogue q₀ plan incoming requests ⊆ U ν)
    (θ : ℝ) (hC : 1 ≤ C) (ell : ℤ)
    (hell : ell ∈ Finset.Ico 0 (selectedPrincipalMicrocellLength F e w i : ℤ)) :
    let p := alignmentMicrocellFirst (selectedPrincipalMicrocellWidth F e w i)
      (F.modulus w) (x (principalAlignmentEmbedding e heM i))
    selectedAlignmentCatalogueKeyPoint e heM i catalogue D r v hv F q₀ w C V U x g a p ell ∈
      selectedAlignmentRouteActualSet
        (selectedAlignmentCatalogueKeyReading e heM i catalogue D r v hv F q₀ w C V U x obs)
        θ q₀ plan b requests (principalPivotRoutes plan) ↔
    p+(F.modulus w:ℤ)*ell ∈ selectedAlignmentRouteActualSet
      (selectedAlignmentRouteRawReading (principalAlignmentEmbedding e heM) i F q₀ w x S)
      θ q₀ plan b requests (principalPivotRoutes plan) := by
  dsimp only
  apply selected_alignment_route_actual_pullback _ _ q₀ plan incoming requests b hb
  intro B b' c stored hmem query hquery
  exact selected_alignment_catalogue_key_reading_microcell e heM i catalogue D r v hv F q₀ w C V U
    x obs g a (fun ν => hqueries ν (selected_alignment_route_query_zero q₀ plan incoming requests))
    hstored hxs hgood S hrecipe B b' c stored query (hcatalogue hmem) (hqueries _ hquery) hC ell hell

end Route

end Hindman168
