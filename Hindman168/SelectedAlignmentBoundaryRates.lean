import Hindman168.MasterMultipliedBoundaryLimit
import Hindman168.AlignedSqrtMicrocellGrowth
import Hindman168.SelectedPrincipalRawLaw
import Hindman168.AlignmentRawPivotSplit

/-! Product-boundary probabilities with the model's gap and the raw pivot
cutoff kept separate. Both are parameters of the ORIGINAL master family;
no master conditions are asserted for a modified or compressed family. -/
namespace Hindman168
open Filter FiniteMass
open scoped Topology Classical BigOperators

/-- The original boundary proof permits any genuine gap index below the raw
pivot. The two indices were previously unnecessarily identified. -/
theorem selected_alignment_multiplied_boundary_tendsto
    {d M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (gap pivot : ℕ → Fin M)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)
    (K modulus : ℕ → ℕ) (J : ℕ) {α : Type*}
    (μ : ℕ → Mass α) (t B : ℕ → α → ℕ)
    (hK : ∀ᶠ w in atTop, K w ≤ F.auxiliary w (gap w).val)
    (hout : ∀ᶠ w in atTop, (∀ x, 0 ≤ μ w x) ∧ total (μ w) = 1 ∧
      ∀ x ∈ (μ w).support, 0 < t w x ∧ (primorial w).Coprime (t w x) ∧ t w x ≤ K w ∧
        B w x ≤ J * K w * alignedSqrtMicrocellWidth (F.gap w (gap w).val) (modulus w)) :
    Tendsto (fun w => event
      (conditionalJoint (μ w) (fun _ => rawMass (F.cutoff w (pivot w).val) (primorial w)))
      (fun xp => ¬ intervalInteriorRoot (F.gap w (gap w).val) (B w xp.1)
        ((t w xp.1 * xp.2 : ℕ) : ℤ))) atTop (𝓝 0) := by
  apply joint_multipliedBoundary_tendsto μ t B
    (fun w => F.cutoff w (pivot w).val) primorial (fun w => F.gap w (gap w).val) K
    (fun w => J * K w * alignedSqrtMicrocellWidth (F.gap w (gap w).val) (modulus w))
  · filter_upwards [hout, hF.nil_boundary_raw_geometry pivot] with w hw hg
    exact ⟨hw.1, hw.2.1, hg.1, primorial_pos w, hF.gap_positive w (gap w).val,
      hg.2.1, hg.2.2, hw.2.2⟩
  · have hm := (master_alignedSqrt_product_margin_tendsto hF gap K modulus hK).const_mul (J : ℝ)
    simpa only [alignedSqrtMicrocellWidth, Nat.cast_mul, mul_assoc, mul_div_assoc, mul_zero] using hm
  · exact hF.nil_boundary_period_ratio_tendsto gap K hK
  · have he := hF.nil_boundary_endpoint_ratio_tendsto gap pivot (fun _ => 1) horder
      (Eventually.of_forall (fun w => (Nat.le_add_left 1 1).trans (F.auxiliary_ge_two w (gap w).val)))
    simpa only [Nat.mul_one] using he

/-- Actual global raw law with a selected tail, padding gap, and principal
pivot. All selected tail indices precede the padding index, so the original
padding auxiliary bound applies. -/
theorem selected_alignment_raw_block_boundary_tendsto
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (i : Fin n)
    (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i) (J : ℕ) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) M)
      (fun x => ¬ intervalInteriorRoot (F.gap w (energyPadding e i))
        (J * F.auxiliary w (energyPadding e i) *
          alignedSqrtMicrocellWidth (F.gap w (energyPadding e i)) (F.modulus w))
        ((principalSubsetProduct T (fun k => x (selectedPrincipalIndex e heM k)) *
          x (selectedPrincipalIndex e heM i) : ℕ) : ℤ))) atTop (𝓝 0) := by
  let gap : Fin M := ⟨energyPadding e i, heM _⟩
  let pivot := selectedPrincipalIndex e heM i
  let tail := T.image (selectedPrincipalIndex e heM)
  have htp : ∀ j ∈ tail, j < pivot := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact (energyPrincipal_strictMono e) (hT k hk)
  have htg : ∀ j ∈ tail, j < gap := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact energyPrincipal_lt_padding e (hT k hk)
  have hg : gap < pivot := energyPadding_lt_principal e i
  have hh := selected_alignment_multiplied_boundary_tendsto hF (fun _ => gap) (fun _ => pivot)
    (Eventually.of_forall (fun _ => hg.le))
    (fun w => F.auxiliary w gap.val) (fun w => F.modulus w) J
    (fun w => alignmentOutsideRawMass F w pivot)
    (fun _ x => alignmentNaturalBlockProduct (insertPivotCoordinate pivot x 1) tail)
    (fun w _ => J * F.auxiliary w gap.val *
      alignedSqrtMicrocellWidth (F.gap w gap.val) (F.modulus w))
    (Eventually.of_forall (fun _ => le_rfl)) (by
      filter_upwards [alignmentOutsideRawMass_geometry hF pivot] with w hw
      refine ⟨hw.1, hw.2.1, ?_⟩
      intro x hx
      have hgeo := hw.2.2 x hx
      refine ⟨Finset.prod_pos (fun j hj => (hgeo j (htp j hj)).1), ?_, ?_, le_rfl⟩
      · exact (alignmentNaturalBlockProduct_coprime _ tail _
          (fun j hj => (hgeo j (htp j hj)).2.2)).symm
      · exact alignment_earlier_block_product_bound hF w gap _
          (fun j hj => (hgeo j (hj.trans hg)).2.1) tail htg)
  have he (w : ℕ) := alignment_raw_pivot_event F w pivot
    (fun x => ¬ intervalInteriorRoot (F.gap w gap.val)
      (J * F.auxiliary w gap.val * alignedSqrtMicrocellWidth (F.gap w gap.val) (F.modulus w))
      ((alignmentNaturalBlockProduct x tail * x pivot : ℕ) : ℤ))
  simp_rw [alignment_block_insert_pivot pivot _ _ 1 tail htp, insertPivotCoordinate_self] at he
  have hblock (x : Fin M → ℕ) : alignmentNaturalBlockProduct x tail =
      principalSubsetProduct T (fun k => x (selectedPrincipalIndex e heM k)) :=
    Finset.prod_image (selectedPrincipalIndex_injective e heM).injOn
  simpa only [hblock] using hh.congr' (Eventually.of_forall (fun w => (he w).symm))

/-- Exact marginalization transfers the discard to the selected raw law;
unused master coordinates are integrated out, not assigned artificial laws. -/
theorem selected_alignment_principal_raw_boundary_tendsto
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (i : Fin n)
    (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i) (J : ℕ) :
    Tendsto (fun w => event (selectedPrincipalRawMass e F w)
      (fun x => ¬ intervalInteriorRoot (F.gap w (energyPadding e i))
        (J * F.auxiliary w (energyPadding e i) *
          alignedSqrtMicrocellWidth (F.gap w (energyPadding e i)) (F.modulus w))
        ((principalSubsetProduct T x * x i : ℕ) : ℤ))) atTop (𝓝 0) := by
  classical
  apply (selected_alignment_raw_block_boundary_tendsto hF e heM i T hT J).congr'
  filter_upwards [hF.selected_principal_raw_law e heM] with w hw
  rw [← hw, event_map]


end Hindman168
