import Hindman168.SelectedAlignmentSourceGeometry
import Hindman168.SelectedAlignmentGeometryView
import Hindman168.AlignmentShortExposureDistance

/-! Padding-gap stability on actual short-exposure fibers. Only mapped
selected letters are tested; unused ambient earlier cutoffs never enter the
bounds. The family view is used as data, without master conditions for it. -/
namespace Hindman168
open Filter
open scoped Topology Classical BigOperators

/-- Same genuine product bin, with its true padding width. -/
theorem selected_alignment_short_key_product_distance
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (w : ℕ) (i : Fin n) (T : Finset (Fin n))
    (hT : ∀ k ∈ T, k < i) {x y : Fin M → ℕ}
    (hx : ∀ k, k < i → x (principalAlignmentEmbedding e heM k) ≤ F.cutoff w (energyPrincipal e k)^2)
    (hpos : ∀ k ∈ T, 0 < x (principalAlignmentEmbedding e heM k))
    (hR : 0 < selectedPrincipalMicrocellWidth F e w i)
    (hkey : alignmentShortExposureKey
        (alignmentGeometryWithGap F (energyPrincipal e i) (energyPadding e i)) w
        (principalAlignmentEmbedding e heM i) (T.image (principalAlignmentEmbedding e heM)) x =
      alignmentShortExposureKey
        (alignmentGeometryWithGap F (energyPrincipal e i) (energyPadding e i)) w
        (principalAlignmentEmbedding e heM i) (T.image (principalAlignmentEmbedding e heM)) y) :
    |((alignmentNaturalBlockProduct y (T.image (principalAlignmentEmbedding e heM)) *
        y (principalAlignmentEmbedding e heM i) : ℕ) : ℤ) -
      ((alignmentNaturalBlockProduct x (T.image (principalAlignmentEmbedding e heM)) *
        x (principalAlignmentEmbedding e heM i) : ℕ) : ℤ)| ≤
      (F.auxiliary w (energyPadding e i) * selectedPrincipalMicrocellWidth F e w i : ℕ) := by
  let tail := T.image (principalAlignmentEmbedding e heM)
  have hl : (∏ j ∈ tail, 2 ^ Nat.log2 (x j)) ≤ F.auxiliary w (energyPadding e i) := by
    apply (Finset.prod_le_prod' (fun j hj => Nat.log2_self_le (show x j ≠ 0 from ?_))).trans
    · rw [show (∏ j ∈ tail, x j) = principalSubsetProduct T
        (fun k => x (principalAlignmentEmbedding e heM k)) from
          alignment_natural_block_product_image _ _ _]
      exact (selected_principal_earlier_product_bound hF e w i _ hx T hT).trans
        (hF.selected_auxiliary_le_padding e w i)
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      exact (hpos k hk).ne'
  have hwidth : 0 < (∏ j ∈ tail, 2 ^ Nat.log2 (x j)) * selectedPrincipalMicrocellWidth F e w i :=
    Nat.mul_pos (Finset.prod_pos (fun _ _ => Nat.pow_pos (by decide))) hR
  have hbin := alignmentShortExposureKey_product_bin _ w _ _ hkey
  simp only [principalAlignmentEmbedding, OrderEmbedding.coe_ofStrictMono,
    selectedPrincipalIndex, alignmentGeometryWithGap_gap, alignmentGeometryWithGap_modulus] at hbin
  have hd := alignment_same_nat_bin_distance hwidth hbin.symm
  exact hd.trans (by exact_mod_cast Nat.mul_le_mul_right (selectedPrincipalMicrocellWidth F e w i) hl)

/-- The actual canonical array has one frozen padding-interval label on the
whole short-exposure fiber, including all fixed selected stored/query slots. -/
theorem selected_alignment_exposure_interval_stable
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (i : Fin n) (q₀ : ℕ) (hq : 0 < q₀) (C : ℕ)
    (V U : Finset (AlignmentAddingPair n i → ℤ)) :
    ∀ᶠ w in atTop, ∀ T : Finset (Fin n), (∀ k ∈ T, k < i) → ∀ x y : Fin M → ℕ,
      (∀ k, k < i → x (principalAlignmentEmbedding e heM k) ≤ F.cutoff w (energyPrincipal e k)^2) →
      (∀ k ∈ T, 0 < x (principalAlignmentEmbedding e heM k)) →
      (∀ k, k < i → y (principalAlignmentEmbedding e heM k) ≤ F.cutoff w (energyPrincipal e k)^2) →
      (∀ j, Nat.Coprime (y j) (primorial w)) →
      alignmentShortExposureKey
        (alignmentGeometryWithGap F (energyPrincipal e i) (energyPadding e i)) w
        (principalAlignmentEmbedding e heM i) (T.image (principalAlignmentEmbedding e heM)) x =
      alignmentShortExposureKey
        (alignmentGeometryWithGap F (energyPrincipal e i) (energyPadding e i)) w
        (principalAlignmentEmbedding e heM i) (T.image (principalAlignmentEmbedding e heM)) y →
      intervalInteriorRoot (F.gap w (energyPadding e i))
        ((C+3) * F.auxiliary w (energyPadding e i) * selectedPrincipalMicrocellWidth F e w i)
        ((alignmentNaturalBlockProduct x (T.image (principalAlignmentEmbedding e heM)) *
          x (principalAlignmentEmbedding e heM i) : ℕ) : ℤ) →
      ∀ stored ∈ V, ∀ query ∈ U, ∀ p : ℤ,
      |p - y (principalAlignmentEmbedding e heM i)| ≤ (C * selectedPrincipalMicrocellWidth F e w i : ℕ) →
      alignmentIntegerArrayArgument y (F.modulus w)
        (fun a => alignmentPairResidue q₀ w (F.modulus w) a y)
        (fun a => alignmentPairProgression q₀ w (F.modulus w) a y)
        (T.image (principalAlignmentEmbedding e heM)) p
        (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) stored)
        (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) query) /
          (F.gap w (energyPadding e i) : ℤ) =
      ((alignmentNaturalBlockProduct x (T.image (principalAlignmentEmbedding e heM)) *
          x (principalAlignmentEmbedding e heM i) : ℕ) : ℤ) / (F.gap w (energyPadding e i) : ℤ) := by
  filter_upwards [selected_alignment_slot_uniform_margin hF e heM i q₀ hq V,
    selected_alignment_progression_uniform_margin hF e heM i q₀ hq U,
    selected_alignment_microcell_polynomial_small hF e i 0 1] with w hv hu hR
  intro T hT x y hx hpos hy hcop hkey hinterior stored hstored query hquery p hp
  have hRpos : 0 < selectedPrincipalMicrocellWidth F e w i := by
    simp only [pow_zero, mul_one] at hR
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hR)
  let R := selectedPrincipalMicrocellWidth F e w i
  let L := F.auxiliary w (energyPadding e i)
  let tail := T.image (principalAlignmentEmbedding e heM)
  let pivot := principalAlignmentEmbedding e heM i
  let ρ : AlignmentAddingPair M pivot → ℕ := fun a => alignmentPairResidue q₀ w (F.modulus w) a y
  let Δ : AlignmentAddingPair M pivot → ℤ := fun a => alignmentPairProgression q₀ w (F.modulus w) a y
  let v := selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) stored
  let u := selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) query
  have hdist := selected_alignment_short_key_product_distance hF e heM w i T hT hx hpos hRpos hkey
  have htail : (alignmentNaturalBlockProduct y tail : ℤ) ≤ L := by
    have hh := (selected_principal_earlier_product_bound hF e w i
      (fun k => y (principalAlignmentEmbedding e heM k)) hy T hT).trans (hF.selected_auxiliary_le_padding e w i)
    rw [← alignment_natural_block_product_image] at hh
    exact_mod_cast hh
  have hL : (2:ℤ) ≤ L := by exact_mod_cast F.auxiliary_ge_two w (energyPadding e i)
  have hslot : |alignmentIntegerSlotShift ρ v| ≤ (R:ℤ) := hv stored hstored y hcop
  have hprog : |(F.modulus w:ℤ) * alignmentIntegerArrayProgression Δ tail u| ≤ (R:ℤ) :=
    hu query hquery y hcop hy T
  have hlocal : |alignmentIntegerArrayArgument y (F.modulus w) ρ Δ tail p v u -
      (alignmentNaturalBlockProduct y tail : ℤ) * y pivot| ≤ ((C+2)*L*R:ℕ) := by
    rw [alignmentIntegerArrayArgument_difference]
    have ha := (abs_add_le (p-(y pivot:ℤ)) (alignmentIntegerSlotShift ρ v)).trans (add_le_add hp hslot)
    have hb := mul_le_mul_of_nonneg_left ha (Int.natCast_nonneg (alignmentNaturalBlockProduct y tail))
    have hc := abs_add_le
      ((alignmentNaturalBlockProduct y tail:ℤ)*(p-y pivot+alignmentIntegerSlotShift ρ v))
      ((F.modulus w:ℤ)*alignmentIntegerArrayProgression Δ tail u)
    rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)] at hc
    have hm := mul_le_mul_of_nonneg_right htail (by positivity : (0:ℤ) ≤ (C*R:ℕ)+(R:ℤ))
    push_cast at hb hm ⊢
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ (L:ℤ)-1) (Int.natCast_nonneg R)]
  have htotal : |alignmentIntegerArrayArgument y (F.modulus w) ρ Δ tail p v u -
      ((alignmentNaturalBlockProduct x tail * x pivot:ℕ):ℤ)| ≤ ((C+3)*L*R:ℕ) := by
    have hh := abs_add_le
      (alignmentIntegerArrayArgument y (F.modulus w) ρ Δ tail p v u -
        (alignmentNaturalBlockProduct y tail:ℤ)*y pivot)
      (((alignmentNaturalBlockProduct y tail * y pivot:ℕ):ℤ)-
        ((alignmentNaturalBlockProduct x tail * x pivot:ℕ):ℤ))
    rw [Nat.cast_mul, sub_add_sub_cancel] at hh
    calc
      _ ≤ (((C+2)*L*R:ℕ):ℤ) + ((L*R:ℕ):ℤ) := hh.trans (add_le_add hlocal hdist)
      _ = _ := by push_cast; ring
  have hh := intervalInteriorRoot_shift_quotient (F.gap w (energyPadding e i)) ((C+3)*L*R)
    (hF.gap_positive w _) _ _ hinterior htotal
  dsimp only [tail, pivot] at hh
  have he : ((alignmentNaturalBlockProduct x (T.image (principalAlignmentEmbedding e heM)) *
      x (principalAlignmentEmbedding e heM i):ℕ):ℤ) +
      (alignmentIntegerArrayArgument y (F.modulus w) ρ Δ
        (T.image (principalAlignmentEmbedding e heM)) p v u -
        ((alignmentNaturalBlockProduct x (T.image (principalAlignmentEmbedding e heM)) *
          x (principalAlignmentEmbedding e heM i):ℕ):ℤ)) =
      alignmentIntegerArrayArgument y (F.modulus w) ρ Δ
        (T.image (principalAlignmentEmbedding e heM)) p v u := by ring
  rw [he] at hh
  exact hh

end Hindman168
