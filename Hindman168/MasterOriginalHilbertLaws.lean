import Hindman168.HarmonicSubprobability
import Hindman168.SubprobabilityHilbertBounds
import Hindman168.MasterSamplingBudgets

/-! The exact original master laws support bounded Hilbert families at
all stages. Eventually all master pivots have probability mass one. -/

namespace Hindman168
open FiniteMass Filter

noncomputable def masterOriginalBoundedFamily (F : MasterParameterFamily)
    (root : ℕ → ℕ) (f : ℕ → ℤ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ w y, |f w y| ≤ B) :
    boundedHilbertFamilies (fun w => FiniteMassL2 (integerMass (F.cutoff w (root w)) (primorial w))) :=
  subprobabilityBoundedFamily _ (fun _ => integerMass_total_le_one _ _) f B hB
    (fun w y _ => hf w y)

theorem MasterParameterConditions.original_masses_eventually_probability {n N : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) :
    ∀ᶠ w in atTop, ∀ j ∈ Finset.range N,
      total (integerMass (F.cutoff w j) (primorial w)) = 1 := by
  exact hF.raw_cutoffs_valid.mono (fun _ hw j hj => integerMass_total (hw j hj).2.2)

theorem MasterParameterConditions.original_masses_uniform_stage {n N : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) :
    ∃ w₀ : ℕ, ∀ w, w₀ ≤ w → ∀ j ∈ Finset.range N,
      total (integerMass (F.cutoff w j) (primorial w)) = 1 :=
  eventually_atTop.mp hF.original_masses_eventually_probability

end Hindman168

