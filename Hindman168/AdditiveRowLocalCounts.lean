import Hindman168.MaskGeneratedAdditiveResidues

/-! Exact local counts for the actual general copied rows under the original
uniform residue law. No conditional independence of row values is assumed. -/

namespace Hindman168.PolynomialRowFamily.AdditiveResidueEliminationConditions

open scoped BigOperators Classical
open FiniteMass

variable {n r m : ℕ} {F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m}
  {master : MasterParameterFamily} {w : ℕ} {c : Fin (m + 1) → ℕ}
  {x : Fin n → ℕ} {target : Fin r} {V : ℕ}

theorem copied_single_zero_mass (H : F.AdditiveResidueEliminationConditions master w c x target V)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hwp : w < p) (hpV : p ≤ V)
    (havoid : ∀ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (x j : ZMod p)) f ≠ 0)
    (A : ℕ)
    (i : CopiedReplicaCubeRow (additiveRowAssigned (Fintype.card (PolynomialRowFamily.OffTargetRow target)))) :
    event (uniformFintypeMass
      (Fin (Fintype.card (AdditiveCopiedColumn (Fintype.card (PolynomialRowFamily.OffTargetRow target)) (m + 1)))
        → ZMod (p ^ A)))
      (fun z => linearRowAddHom
        (fun j => (H.elimination.data.copiedFinCoefficient i j : ZMod (p ^ A))) z = 0) =
      ((p ^ A : ℕ) : ℝ)⁻¹ :=
  primePower_primitive_row_zero_mass hp (H.elimination.data.copiedFinCoefficient i)
    (H.copiedFin_primitive p hp hwp hpV havoid i)

theorem copied_pair_zero_mass (H : F.AdditiveResidueEliminationConditions master w c x target V)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hwp : w < p) (hpV : p ≤ V)
    (havoid : ∀ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun k => (x k : ZMod p)) f ≠ 0)
    (A B C : ℕ) (hBA : B ≤ A) (hCA : C ≤ A)
    (i j : CopiedReplicaCubeRow (additiveRowAssigned (Fintype.card (PolynomialRowFamily.OffTargetRow target))))
    (hij : i ≠ j) :
    event (uniformFintypeMass
      (Fin (Fintype.card (AdditiveCopiedColumn (Fintype.card (PolynomialRowFamily.OffTargetRow target)) (m + 1)))
        → ZMod (p ^ A)))
      (fun z => ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B))
          (linearRowAddHom (fun k => (H.elimination.data.copiedFinCoefficient i k : ZMod (p ^ A))) z) = 0 ∧
        ZMod.castHom (pow_dvd_pow p hCA) (ZMod (p ^ C))
          (linearRowAddHom (fun k => (H.elimination.data.copiedFinCoefficient j k : ZMod (p ^ A))) z) = 0) =
      ((p ^ (B + C) : ℕ) : ℝ)⁻¹ :=
  primePower_twoRow_mass_of_linearIndependent hp hBA hCA
    (H.elimination.data.copiedFinCoefficient i) (H.elimination.data.copiedFinCoefficient j)
    (H.copiedFin_pair_independent p hp hwp hpV havoid i j hij)

end Hindman168.PolynomialRowFamily.AdditiveResidueEliminationConditions
