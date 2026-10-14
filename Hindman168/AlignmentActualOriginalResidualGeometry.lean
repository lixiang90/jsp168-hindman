import Hindman168.OriginalIntegerResidualBoxGeometry
import Hindman168.AlignmentCubeBoxCoordinates
import Hindman168.AlignmentRawRetainedScale

/-! EXACT original transformed cube endpoints, before any endpoint changes,
satisfy native residual geometry for every retained subset under actual raw
supports. Normalization growth and residue bounds are derived explicitly. -/
namespace Hindman168
open Filter
open scoped Topology

noncomputable def alignmentOriginalResidualUpper (tailCount K : ℕ) (C : ℝ) : ℝ :=
  max ((2 : ℝ)^tailCount*(2*C+1)) ((2 : ℝ)^tailCount*((K : ℝ)+1)+3)

theorem alignment_actual_original_residual_geometry_eventually {κ : Type*}
    {N k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (i : Fin N) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C+1 ≤ (K : ℝ)) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      ∀ L H : Option κ → ℝ,
      (∀ j, |L j| ≤ C*alignmentLocalLength F w i ∧
        |H j| ≤ C*alignmentLocalLength F w i ∧ c*alignmentLocalLength F w i ≤ H j-L j) →
      ∀ U : Finset (Fin N), U ⊆ T → ∀ a : Option κ → ℤ,
      (∀ j, 0 ≤ a j ∧ a j < (d*alignmentNaturalBlockProduct x U : ℕ)) →
      let q : ℕ := d*alignmentNaturalBlockProduct x U
      let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (x i)
      let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
      let lo := fun j => (alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct x T) p Y j ⌈L j⌉ : ℝ)
      let hi := fun j => (alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct x T) p Y j ⌈H j⌉ : ℝ)
      let Z := alignmentCubeScale F w i T x/(q : ℝ)
      ∀ j, (c/2)*Z ≤ (hi j-(a j : ℝ))/(q : ℝ)-(lo j-(a j : ℝ))/(q : ℝ) ∧
        (hi j-(a j : ℝ))/(q : ℝ)-(lo j-(a j : ℝ))/(q : ℝ) ≤ alignmentOriginalResidualUpper T.card K C*Z ∧
        |(lo j-(a j : ℝ))/(q : ℝ)| ≤ alignmentOriginalResidualUpper T.card K C*Z ∧
        |(hi j-(a j : ℝ))/(q : ℝ)| ≤ alignmentOriginalResidualUpper T.card K C*Z := by
  filter_upwards [alignment_actual_rounded_box_geometry_eventually (ι := κ) hF i T c C K hc hC hK,
    alignment_retained_scale_eventually hF i T d hd 0 (eps := 1) (by norm_num),
    alignmentGlobalRawMass_geometry hF] with w hg hs hraw
  intro x hx L H hbox U hU a ha
  dsimp only
  have hpos := fun j (_hj : j ∈ T) => alignmentGlobalRawMass_support_positive hF w x hx j
  have hret : 0 < alignmentNaturalBlockProduct x U := Finset.prod_pos (fun j hj => hpos j (hU hj))
  have hretAux := alignment_earlier_block_product_bound hF w i x (fun j _ => hraw.2.2 x hx j) U
    (fun j hj => hT j (hU hj))
  have hscale := hs x (alignmentNaturalBlockProduct x U) 0 hret hretAux (Nat.zero_le _)
  simp only [pow_zero,one_mul] at hscale
  have hqR : (0 : ℝ) < (d : ℝ)*alignmentNaturalBlockProduct x U := by positivity
  have hZ : ((d*alignmentNaturalBlockProduct x U : ℕ) : ℝ) ≤ alignmentCubeScale F w i T x := by
    have hh := (le_div_iff₀ hqR).mp hscale
    simpa only [one_mul,Nat.cast_mul] using hh
  have hgeom := hg x hpos L H hbox
  dsimp only at hgeom
  have hh := original_integer_residual_box_geometry _ _ a (d*alignmentNaturalBlockProduct x U)
    (Nat.mul_pos hd hret) (alignmentCubeScale F w i T x) (c/2)
    ((2 : ℝ)^T.card*((K : ℝ)+1)+2) ((2 : ℝ)^T.card*(2*C+1)) hZ ha
    (by simpa only [Int.cast_sub] using hgeom)
  simpa only [alignmentOriginalResidualUpper,add_assoc,show (2 : ℝ)+1=3 by norm_num] using hh

end Hindman168
