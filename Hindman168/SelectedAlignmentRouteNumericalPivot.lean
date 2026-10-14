import Hindman168.SelectedAlignmentRouteNumerical

/-! The signed route pivot can be made a natural coordinate without changing
any earlier raw input. Residues and progression shifts are proved insensitive
to this update because every adding pair lies strictly before the pivot. -/
namespace Hindman168
open scoped BigOperators Classical

theorem alignment_block_product_eq_of_earlier_eq {M : ℕ} {i : Fin M}
    {x y : Fin M → ℕ} (hxy : ∀ j < i, x j = y j)
    (T : Finset (Fin M)) (hT : ∀ j ∈ T, j < i) :
    alignmentNaturalBlockProduct x T = alignmentNaturalBlockProduct y T := by
  exact Finset.prod_congr rfl (fun j hj => hxy j (hT j hj))

theorem alignment_numerator_eq_of_earlier_eq {M : ℕ} {i : Fin M}
    {x y : Fin M → ℕ} (hxy : ∀ j < i, x j = y j)
    (q₀ w : ℕ) (e : AlignmentAddingPair M i) :
    alignmentIntegerNumerator q₀ w e x = alignmentIntegerNumerator q₀ w e y := by
  unfold alignmentIntegerNumerator
  rw [alignment_block_product_eq_of_earlier_eq hxy _ (alignmentPair_source_before e)]

theorem alignment_residue_eq_of_earlier_eq {M : ℕ} {i : Fin M}
    {x y : Fin M → ℕ} (hxy : ∀ j < i, x j = y j)
    (q₀ w modulus : ℕ) (e : AlignmentAddingPair M i) :
    alignmentPairResidue q₀ w modulus e x = alignmentPairResidue q₀ w modulus e y := by
  unfold alignmentPairResidue
  rw [alignment_numerator_eq_of_earlier_eq hxy,
    alignment_block_product_eq_of_earlier_eq hxy _ (alignmentPair_target_before e)]

theorem alignment_progression_eq_of_earlier_eq {M : ℕ} {i : Fin M}
    {x y : Fin M → ℕ} (hxy : ∀ j < i, x j = y j)
    (q₀ w modulus : ℕ) (e : AlignmentAddingPair M i) :
    alignmentPairProgression q₀ w modulus e x = alignmentPairProgression q₀ w modulus e y := by
  unfold alignmentPairProgression
  rw [alignment_numerator_eq_of_earlier_eq hxy,
    alignment_block_product_eq_of_earlier_eq hxy _ (alignmentPair_target_before e),
    alignment_residue_eq_of_earlier_eq hxy]

theorem selected_alignment_signed_observation_earlier_eq {n M : ℕ} {κ : Type*}
    (f : Fin n ↪o Fin M) (i : Fin n) (F : MasterParameterFamily) (q₀ w : ℕ)
    (x y : Fin M → ℕ) (hxy : ∀ j < f i, x j = y j)
    (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ) (p : ℤ)
    (B : Finset (Fin n)) (hB : ∀ j ∈ B.erase i, j < i)
    (a : ℚ) (u : Multiplicative (AlignmentAddingPair M (f i) → ℤ)) (c : κ) :
    selectedAlignmentSignedScaleObservation f i F q₀ w x S p B a u c =
      selectedAlignmentSignedScaleObservation f i F q₀ w y S p B a u c := by
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
  simp only [selectedAlignmentSignedScaleObservation, alignmentIntegerArrayArgument,
    alignment_block_product_eq_of_earlier_eq hxy _ hT, hρ, hΔ]

/-- Only the pivot coordinate is replaced; all earlier raw data stay literal. -/
theorem selected_alignment_pivot_update_earlier {n M : ℕ}
    (f : Fin n ↪o Fin M) (i : Fin n) (x : Fin M → ℕ) (p : ℕ) :
    ∀ j < f i, x j = Function.update x (f i) p j := by
  intro j hj
  exact (Function.update_of_ne (ne_of_lt hj) p x).symm

theorem selected_alignment_signed_request_nat_update {n M : ℕ} {κ : Type*}
    (f : Fin n ↪o Fin M) (i : Fin n) (F : MasterParameterFamily) (q₀ w : ℕ)
    (x : Fin M → ℕ) (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ)
    (p : ℤ) (hp : 0 ≤ p) (b : Fin n → ℚ) (θ : ℝ)
    (request : AlignmentPivotRequest n i) :
    principalThresholdRequestHolds q₀ b (principalNativeLetter f)
      (selectedAlignmentSignedScaleObservation f i F q₀ w x S p) θ 1 request ↔
    principalThresholdRequestHolds q₀ b (principalNativeLetter f)
      (selectedAlignmentSignedScaleObservation f i F q₀ w
        (Function.update x (f i) p.toNat) S
        ((Function.update x (f i) p.toNat) (f i))) θ 1 request := by
  have hi : i ∉ request.tail := fun hi => (lt_irrefl i) (request.before i hi)
  have hB : ∀ j ∈ (insert i request.tail).erase i, j < i := by
    simpa only [Finset.erase_insert hi] using request.before
  simp only [Function.update_self, Int.toNat_of_nonneg hp]
  unfold principalThresholdRequestHolds
  simp only [selected_alignment_signed_observation_earlier_eq f i F q₀ w x
    (Function.update x (f i) p.toNat) (selected_alignment_pivot_update_earlier f i x p.toNat)
    S p (insert i request.tail) hB]

/-- At nonnegative shifted pivots the real prelimit route event secures the
requests on a natural raw sample obtained by changing exactly that pivot. -/
theorem selected_alignment_route_raw_actual_nat {n M : ℕ} {κ : Type*}
    (f : Fin n ↪o Fin M) (i : Fin n) (F : MasterParameterFamily) (q₀ w : ℕ)
    (x : Fin M → ℕ) (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ)
    (θ : ℝ) (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i))
    (routes : Finset (List (ℕ × List (AlignmentAddingPair n i × ℚ)))) (p : ℤ)
    (hboundary : ∀ route ∈ routes, 0 ≤ p+alignmentIntegerSlotShift
      (fun e => alignmentPairResidue q₀ w (F.modulus w) e x)
      (selectedAlignmentSlotExtension f (alignmentJointRouteArithmetic q₀ plan b route).2.toAdd))
    (hp : p ∈ selectedAlignmentRouteActualSet (selectedAlignmentRouteRawReading f i F q₀ w x S)
      θ q₀ plan b requests routes) :
    ∃ route ∈ routes,
      let arithmetic := alignmentJointRouteArithmetic q₀ plan b route
      let pivot := p+alignmentIntegerSlotShift
        (fun e => alignmentPairResidue q₀ w (F.modulus w) e x)
        (selectedAlignmentSlotExtension f arithmetic.2.toAdd)
      let y := Function.update x (f i) pivot.toNat
      (y (f i) : ℤ) = pivot ∧ (∀ j < f i, y j = x j) ∧
      ∀ request ∈ requests, principalThresholdRequestHolds q₀ arithmetic.1 (principalNativeLetter f)
        (selectedAlignmentSignedScaleObservation f i F q₀ w y S (y (f i))) θ 1 request := by
  obtain ⟨route,hr,hreq⟩ := (selected_alignment_route_raw_actual_iff f i F q₀ w x S
    θ plan b requests routes p).mp hp
  refine ⟨route,hr,?_,?_,?_⟩
  · simpa only [Function.update_self] using Int.toNat_of_nonneg (hboundary route hr)
  · intro j hj
    exact (selected_alignment_pivot_update_earlier f i x _ j hj).symm
  · intro request hrequest
    exact (selected_alignment_signed_request_nat_update f i F q₀ w x S _
      (hboundary route hr) _ θ request).mp (hreq request hrequest)

/-- The pre-existing finite-scale observation is the same signed observation
at a natural pivot, after the explicit finite-scale membership gate. -/
theorem selected_alignment_signed_observation_eq_native_scale {n M r : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (F : MasterParameterFamily)
    (A : Finset ℚ)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (q₀ w : ℕ) (x : Fin M → ℕ) (i : Fin n) :
    selectedAlignmentSignedScaleObservation (principalAlignmentEmbedding e heM) i F q₀ w x
      (fun T a c w z => if ha : a ∈ A then S T i (⟨a,ha⟩,c) w z else 0)
      (x (selectedPrincipalIndex e heM i)) =
    principalNativeScaleObservation e heM F A S q₀ w x i := by
  funext B a u c
  by_cases ha : a ∈ A <;>
    simp only [selectedAlignmentSignedScaleObservation, principalNativeScaleObservation,
      ha, dite_true, dite_false]

/-- The literal route event specializes to the already secured finite-scale
native predicate, on the same raw sample with only its pivot changed. -/
theorem selected_alignment_route_native_scale_requests {n M r : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (F : MasterParameterFamily)
    (A : Finset ℚ)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (q₀ w : ℕ) (x : Fin M → ℕ) (i : Fin n)
    (θ : ℝ) (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i))
    (routes : Finset (List (ℕ × List (AlignmentAddingPair n i × ℚ)))) (p : ℤ)
    (hboundary : ∀ route ∈ routes, 0 ≤ p+alignmentIntegerSlotShift
      (fun a => alignmentPairResidue q₀ w (F.modulus w) a x)
      (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM)
        (alignmentJointRouteArithmetic q₀ plan b route).2.toAdd))
    (hp : p ∈ selectedAlignmentRouteActualSet
      (selectedAlignmentRouteRawReading (principalAlignmentEmbedding e heM) i F q₀ w x
        (fun T a c w z => if ha : a ∈ A then S T i (⟨a,ha⟩,c) w z else 0))
      θ q₀ plan b requests routes) :
    ∃ route ∈ routes,
      let arithmetic := alignmentJointRouteArithmetic q₀ plan b route
      let pivot := p+alignmentIntegerSlotShift
        (fun a => alignmentPairResidue q₀ w (F.modulus w) a x)
        (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) arithmetic.2.toAdd)
      let y := Function.update x (selectedPrincipalIndex e heM i) pivot.toNat
      (y (selectedPrincipalIndex e heM i) : ℤ) = pivot ∧
      (∀ j < selectedPrincipalIndex e heM i, y j = x j) ∧
      ∀ request ∈ requests, principalThresholdRequestHolds q₀ arithmetic.1
        (principalNativeLetter (principalAlignmentEmbedding e heM))
        (principalNativeScaleObservation e heM F A S q₀ w y i) θ 1 request := by
  obtain ⟨route,hr,heq,hearlier,hreq⟩ := selected_alignment_route_raw_actual_nat
    (principalAlignmentEmbedding e heM) i F q₀ w x
    (fun T a c w z => if ha : a ∈ A then S T i (⟨a,ha⟩,c) w z else 0)
    θ plan b requests routes p hboundary hp
  refine ⟨route,hr,heq,hearlier,?_⟩
  intro request hrequest
  rw [← selected_alignment_signed_observation_eq_native_scale]
  exact hreq request hrequest

end Hindman168
