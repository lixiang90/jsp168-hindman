import Hindman168.AlignmentJointTailRemovalPosterior

/-! The finite original residue choices may be selected after the exposure.
The failure union still vanishes uniformly under the ACTUAL posterior;
the finite list is fixed before the analytic cutoff. -/
namespace Hindman168
open Module Filter FiniteMass
open scoped Manifold ContDiff BigOperators Classical
universe u

variable {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

theorem alignment_joint_tail_removal_finite_residue_choices
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (c C η : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (hη : 0 < η)
    (slots : ι → AlignmentAddingPair N i → ℤ) (B : ι → ℝ) (L : ι → NNReal)
    {χ : Type*} [Fintype χ] {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      alignmentTypicalShortPosterior F w i T x →
      ∀ U : T → Finset (Fin N), (∀ j, U j ⊆ T ∧ j.val ∉ U j) →
      ∀ (q₀ : ℕ) (Y rho : ℤ) (residueChoice : χ → T → Option κ → ℤ)
        (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G),
      event (conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
        (fun y => alignmentShortExposureKey F w i T y=alignmentShortExposureKey F w i T x))
        (fun y => ∃ choice : χ, ∃ j : T, alignmentJointTailRemovalEvent D n v hv r b F q₀ w T (U j) x j d
          Y rho (residueChoice choice j) shift slots weight g a B L c C η (fun k : T => y k.val)) < ε := by
  let C₀ : ℝ := (3*2^T.card)*(T.card : ℝ)
  let δ := ε/((Fintype.card χ : ℝ)*C₀+1)
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hδ : 0 < δ := div_pos hε (by positivity)
  have he : ((Fintype.card χ : ℝ)*C₀+1)*δ=ε := by dsimp only [δ]; field_simp
  have hh := alignment_joint_tail_removal_posterior_union_bound (κ := κ) D n v hv r b
    hF T hT d hd c C η hc hC hη slots B L hδ
  filter_upwards [hh,alignmentGlobalRawMass_geometry hF] with w hw hg
  intro x hx htyp U hU q₀ Y rho residueChoice shift weight g a
  let μ := conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
    (fun y => alignmentShortExposureKey F w i T y=alignmentShortExposureKey F w i T x)
  let E : χ → (Fin N → ℕ) → Prop := fun choice y => ∃ j : T,
    alignmentJointTailRemovalEvent D n v hv r b F q₀ w T (U j) x j d Y rho
      (residueChoice choice j) shift slots weight g a B L c C η (fun k : T => y k.val)
  have hunion := event_union_bound μ Finset.univ E (conditionMass_nonneg _ _ hg.1)
  have hbound : event μ (fun y => ∃ choice : χ, E choice y) ≤ (Fintype.card χ : ℝ)*C₀*δ := by
    have hchange : (fun y => ∃ choice : χ, E choice y)=(fun y => ∃ choice ∈ (Finset.univ : Finset χ), E choice y) := by
      funext y; simp
    rw [hchange]
    apply hunion.trans
    calc
      _ ≤ ∑ _choice : χ, C₀*δ := Finset.sum_le_sum (fun choice _ =>
        hw x hx htyp U hU q₀ Y rho (residueChoice choice) shift weight g a)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc]
  change event μ (fun y => ∃ choice : χ, E choice y) < ε
  nlinarith

end Hindman168
