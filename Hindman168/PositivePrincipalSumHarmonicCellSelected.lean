import Hindman168.PositivePrincipalSumHarmonicCellTransfer
import Hindman168.SelectedPrincipalMicrocellGrowth

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Topology Classical

/-- The actual selected model uses the padding microcell and principal
cutoff. Uniform local coverage transfers to the original harmonic kernel
on every complete cell, with constants fixed before models or tolerances. -/
theorem principal_selected_microcell_cover_transfer
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (i : Fin n)
    {V : Type*} [Fintype V] (Q : ℕ) (hQ : 0 < Q) :
    ∀ᶠ w in atTop, ∀ p : ℕ, p.Coprime (primorial w) →
      F.cutoff w (energyPrincipal e i) ≤
        (p / selectedPrincipalMicrocellWidth F e w i) * selectedPrincipalMicrocellWidth F e w i →
      (p / selectedPrincipalMicrocellWidth F e w i) * selectedPrincipalMicrocellWidth F e w i +
        selectedPrincipalMicrocellWidth F e w i ≤ F.cutoff w (energyPrincipal e i)^2 →
      ∀ P : V → ℤ → Prop,
      3 / (4 * (Q : ℝ)) ≤ event (uniformIntervalMass 0 (selectedPrincipalMicrocellLength F e w i))
        (fun ell => ∃ v, P v (alignmentMicrocellFirst
          (selectedPrincipalMicrocellWidth F e w i) (F.modulus w) p + (F.modulus w : ℤ)*ell)) →
      1 / (2 * (Q : ℝ)) ≤ ∑ v, event
        (conditionMass (integerMass (F.cutoff w (energyPrincipal e i)) (primorial w))
          (fun z => principalMicrocellExposure (selectedPrincipalMicrocellWidth F e w i)
            (F.modulus w) z = principalMicrocellExposure (selectedPrincipalMicrocellWidth F e w i)
            (F.modulus w) p)) (P v) := by
  have he := (selected_principal_microcell_cutoff_ratio hF e i).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1/(4*(Q : ℝ)) by positivity))
  have hl := (selected_principal_microcell_length_tendsto hF e i).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [he, hl, hF.raw_cutoffs_valid, hF.primorial_dvd_modulus]
    with w he hl hv hWM p hp hlo hhi P hcover
  have hq : 0 < selectedPrincipalMicrocellLength F e w i := by exact_mod_cast (show (0 : ℝ) < selectedPrincipalMicrocellLength F e w i by linarith)
  let r : Fin (F.modulus w : ℕ) := ⟨p % (F.modulus w : ℕ), Nat.mod_lt _ (F.modulus w).pos⟩
  have hr : r.val.Coprime (primorial w) := (residue_coprime_iff _ _ _ _ hWM rfl).mp hp
  have hres : (p : ℤ) % (F.modulus w : ℕ) = r.val := by
    exact_mod_cast (rfl : p % (F.modulus w : ℕ) = r.val)
  have hh := principal_microcell_uniform_cover_transfer (F.cutoff w (energyPrincipal e i))
    (primorial w) (F.modulus w) (selectedPrincipalMicrocellLength F e w i) Q p r
    (hF.cutoff_positive w _) (F.modulus w).pos hq hQ hWM hr hres
    (hv _ (Finset.mem_range.mpr (heM _))).2.2
    (by rw [selected_principal_microcell_exact]; exact_mod_cast hlo)
    (by rw [selected_principal_microcell_exact]; exact_mod_cast hhi) P
    (by rw [selected_principal_microcell_exact]; exact he.le)
    (by simpa only [selected_principal_microcell_exact] using hcover)
  simpa only [selected_principal_microcell_exact] using hh
end Hindman168
