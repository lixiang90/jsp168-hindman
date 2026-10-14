import Hindman168.AlignmentJointOriginalBoxRemovalPosterior

/-! COMPLETE permitted-box removal failure vanishes after the union over any
fixed finite original residue-choice list, even selected after the exposure.
The list cardinality precedes the analytic cutoff and empty lists stay empty. -/
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

theorem alignment_joint_original_box_removal_finite_choices
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C+1 ≤ (K : ℝ))
    (slots : ι → AlignmentAddingPair N i → ℤ) (B : ι → ℝ) (L : ι → NNReal)
    {χ : Type*} [Fintype χ] {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      alignmentTypicalShortPosterior F w i T x →
      ∀ (q₀ : ℕ) (rho : ℤ) (residueChoice : χ → Option κ → ℤ)
        (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G),
      let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
      event (conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
        (fun y => alignmentShortExposureKey F w i T y=alignmentShortExposureKey F w i T x))
        (fun y => ∃ choice : χ, alignmentJointOriginalBoxRemovalFailure D n v hv r b F q₀ w T x d Y rho (residueChoice choice)
          shift slots weight g a B L c C ε y) < δ := by
  let δ' := δ/((Fintype.card χ : ℝ)+1)
  have hδ' : 0 < δ' := div_pos hδ (by positivity)
  have he : ((Fintype.card χ : ℝ)+1)*δ'=δ := by dsimp only [δ']; field_simp
  have hh := alignment_joint_original_box_removal_posterior_vanishing (κ := κ) D n v hv r b
    hF T hT d hd c C K hc hC hK slots B L hε hδ'
  filter_upwards [hh,alignmentGlobalRawMass_geometry hF] with w hw hraw
  intro x hx htyp q₀ rho residueChoice shift weight g a
  dsimp only
  let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
  let μ := conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
    (fun y => alignmentShortExposureKey F w i T y=alignmentShortExposureKey F w i T x)
  let E : χ → (Fin N → ℕ) → Prop := fun choice =>
    alignmentJointOriginalBoxRemovalFailure D n v hv r b F q₀ w T x d Y rho (residueChoice choice)
      shift slots weight g a B L c C ε
  have hbound : event μ (fun y => ∃ choice : χ, E choice y) ≤ (Fintype.card χ : ℝ)*δ' := by
    have heq : (fun y => ∃ choice : χ, E choice y)=(fun y => ∃ choice ∈ (Finset.univ : Finset χ), E choice y) := by
      funext y; simp
    rw [heq]
    apply (event_union_bound μ Finset.univ E (conditionMass_nonneg _ _ hraw.1)).trans
    calc
      _ ≤ ∑ _choice : χ, δ' := Finset.sum_le_sum (fun choice _ =>
        (hw x hx htyp q₀ rho (residueChoice choice) shift weight g a).le)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change event μ (fun y => ∃ choice : χ, E choice y) < δ
  nlinarith

end Hindman168
