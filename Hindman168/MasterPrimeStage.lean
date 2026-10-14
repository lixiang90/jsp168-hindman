import Hindman168.EquidistributedPrimePool
import Hindman168.GapRequirements
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.PNat.Basic

/-!
# Sequential actual prime/gap/cutoff arithmetic stages

The history contains all earlier positive gaps and their cutoffs. At each
stage V and Q are fixed first, followed by the prime pool, the finite LCM
gap, and the dyadic cutoff. The exponent e0 is a supplied natural number;
existence of e0 with the paper's small-prime probability property is a
separate theorem, not assumed by this arithmetic construction.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology

abbrev MasterPrimeHistory := List (ℕ+ × ℕ)

def masterStageAuxiliary (M : ℕ+) (history : MasterPrimeHistory) : ℕ :=
  2 + (M : ℕ) + (history.map (fun z => z.2 ^ 2)).prod

theorem masterStageAuxiliary_ge_two (M : ℕ+) (history : MasterPrimeHistory) :
    2 ≤ masterStageAuxiliary M history := by unfold masterStageAuxiliary; omega

theorem masterStageAuxiliary_ge_one (M : ℕ+) (history : MasterPrimeHistory) :
    1 ≤ masterStageAuxiliary M history := (by decide : 1 ≤ 2).trans (masterStageAuxiliary_ge_two M history)

def masterStageModulus (w e0 V : ℕ) : ℕ :=
  (primorial w) ^ e0 * ∏ p ∈ (Finset.Icc (w + 1) V).filter Nat.Prime, p

theorem masterStageModulus_pos (w e0 V : ℕ) : 0 < masterStageModulus w e0 V := by
  apply Nat.mul_pos (Nat.pow_pos (primorial_pos w))
  apply Finset.prod_pos
  intro p hp
  exact (Finset.mem_filter.mp hp).2.pos

noncomputable def masterStagePool (w e0 : ℕ) (M : ℕ+) (history : MasterPrimeHistory) :
    DyadicPrimePool :=
  equidistributedGrowingPrimePool (masterStageAuxiliary M history)
    (masterStageModulus w e0 (masterStageAuxiliary M history)) w
    (masterStageModulus_pos _ _ _)

noncomputable def masterStageEarlier (history : MasterPrimeHistory) : Finset ℕ := by
  classical
  exact history.toFinset.image (fun z => (z.1 : ℕ))

theorem masterStageEarlier_pos (history : MasterPrimeHistory) :
    ∀ n ∈ masterStageEarlier history, 0 < n := by
  classical
  intro n hn
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hn
  exact z.1.pos

theorem masterStageEarlier_mem {history : MasterPrimeHistory} {z : ℕ+ × ℕ}
    (hz : z ∈ history) : (z.1 : ℕ) ∈ masterStageEarlier history := by
  classical
  exact Finset.mem_image.mpr ⟨z, List.mem_toFinset.mpr hz, rfl⟩

noncomputable def masterStageGap {m : ℕ} (w e0 : ℕ) (M : ℕ+)
    (D : Finset (MvPolynomial (Fin m) ℤ)) (history : MasterPrimeHistory) : ℕ :=
  polynomialGap M (masterStageEarlier history) D
    (primePool (masterStagePool w e0 M history).lower (masterStagePool w e0 M history).upper)
    ((masterStagePool w e0 M history).upper + masterStageAuxiliary M history) w

theorem masterStageGap_pos {m : ℕ} (w e0 : ℕ) (M : ℕ+)
    (D : Finset (MvPolynomial (Fin m) ℤ)) (history : MasterPrimeHistory) :
    0 < masterStageGap w e0 M D history :=
  polynomialGap_pos M.pos (masterStageEarlier_pos history) _ _ _ _

theorem masterStageGap_modulus_dvd {m : ℕ} (w e0 : ℕ) (M : ℕ+)
    (D : Finset (MvPolynomial (Fin m) ℤ)) (history : MasterPrimeHistory) :
    (M : ℕ) ∣ masterStageGap w e0 M D history :=
  polynomialGap_modulus_dvd _ _ _ _ _ _

theorem masterStageGap_earlier_dvd {m : ℕ} (w e0 : ℕ) (M : ℕ+)
    (D : Finset (MvPolynomial (Fin m) ℤ)) {history : MasterPrimeHistory} {z : ℕ+ × ℕ}
    (hz : z ∈ history) : (z.1 : ℕ) ∣ masterStageGap w e0 M D history :=
  polynomialGap_earlier_dvd _ (masterStageEarlier_mem hz) _ _ _ _

theorem masterStageGap_value_dvd {m : ℕ} (w e0 : ℕ) (M : ℕ+)
    {D : Finset (MvPolynomial (Fin m) ℤ)} (history : MasterPrimeHistory)
    {d : MvPolynomial (Fin m) ℤ} {p : Fin m → ℕ} (hd : d ∈ D)
    (hp : ∀ i, p i ∈ primePool (masterStagePool w e0 M history).lower
      (masterStagePool w e0 M history).upper)
    (hv : MvPolynomial.eval (fun i => (p i : ℤ)) d ≠ 0) :
    (M : ℕ) * (MvPolynomial.eval (fun i => (p i : ℤ)) d).natAbs ∣
      masterStageGap w e0 M D history :=
  polynomialGap_value_dvd _ _ hd hp hv _ _

theorem masterStageGap_lower {m : ℕ} (w e0 : ℕ) (M : ℕ+)
    (D : Finset (MvPolynomial (Fin m) ℤ)) (history : MasterPrimeHistory) :
    w * ((masterStagePool w e0 M history).upper + masterStageAuxiliary M history) ^ w ≤
      masterStageGap w e0 M D history :=
  polynomialGap_lower M.pos (masterStageEarlier_pos history) _ _ _ _

noncomputable def masterStageCutoff {m : ℕ} (w e0 : ℕ) (M : ℕ+)
    (D : Finset (MvPolynomial (Fin m) ℤ)) (history : MasterPrimeHistory) : ℕ :=
  dyadicHarmonicCutoff (masterStageGap w e0 M D history) w

theorem masterStageCutoff_log_lower {m : ℕ} (w e0 : ℕ) (M : ℕ+)
    (D : Finset (MvPolynomial (Fin m) ℤ)) (history : MasterPrimeHistory) :
    (w : ℝ) * (masterStageGap w e0 M D history : ℝ) ^ w ≤
      Real.log (masterStageCutoff w e0 M D history) :=
  dyadicHarmonicCutoff_log_lower _ _

theorem masterStageCutoff_power_two {m : ℕ} (w e0 : ℕ) (M : ℕ+)
    (D : Finset (MvPolynomial (Fin m) ℤ)) (history : MasterPrimeHistory) :
    ∃ n : ℕ, masterStageCutoff w e0 M D history = 2 ^ n := ⟨_, rfl⟩

noncomputable def masterPrimeHistory {m : ℕ} (w e0 : ℕ) (M : ℕ+)
    (D : Finset (MvPolynomial (Fin m) ℤ)) : ℕ → MasterPrimeHistory
  | 0 => []
  | l + 1 =>
      let history := masterPrimeHistory w e0 M D l
      (⟨masterStageGap w e0 M D history, masterStageGap_pos w e0 M D history⟩,
        masterStageCutoff w e0 M D history) :: history

theorem masterPrimeHistory_length {m : ℕ} (w e0 : ℕ) (M : ℕ+)
    (D : Finset (MvPolynomial (Fin m) ℤ)) (l : ℕ) :
    (masterPrimeHistory w e0 M D l).length = l := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [masterPrimeHistory, List.length_cons, ih]

theorem masterPrimeHistory_contains {m : ℕ} (w e0 : ℕ) (M : ℕ+)
    (D : Finset (MvPolynomial (Fin m) ℤ)) {j l : ℕ} (hjl : j < l) :
    (⟨masterStageGap w e0 M D (masterPrimeHistory w e0 M D j),
      masterStageGap_pos w e0 M D (masterPrimeHistory w e0 M D j)⟩,
      masterStageCutoff w e0 M D (masterPrimeHistory w e0 M D j)) ∈
        masterPrimeHistory w e0 M D l := by
  induction l with
  | zero => omega
  | succ l ih =>
    rw [masterPrimeHistory, List.mem_cons]
    by_cases hj : j = l
    · subst j; exact Or.inl rfl
    · exact Or.inr (ih (by omega))

theorem masterPrimeHistory_gap_dvd {m : ℕ} (w e0 : ℕ) (M : ℕ+)
    (D : Finset (MvPolynomial (Fin m) ℤ)) {j l : ℕ} (hjl : j < l) :
    masterStageGap w e0 M D (masterPrimeHistory w e0 M D j) ∣
      masterStageGap w e0 M D (masterPrimeHistory w e0 M D l) :=
  masterStageGap_earlier_dvd w e0 M D (masterPrimeHistory_contains w e0 M D hjl)

theorem masterPrimeHistory_cutoff_product {m : ℕ} (w e0 : ℕ) (M : ℕ+)
    (D : Finset (MvPolynomial (Fin m) ℤ)) (l : ℕ) :
    ((masterPrimeHistory w e0 M D l).map (fun z => z.2 ^ 2)).prod =
      ∏ j ∈ Finset.range l, (masterStageCutoff w e0 M D (masterPrimeHistory w e0 M D j)) ^ 2 := by
  induction l with
  | zero => simp only [masterPrimeHistory, List.map_nil, List.prod_nil, Finset.range_zero, Finset.prod_empty]
  | succ l ih =>
    simp only [masterPrimeHistory, List.map_cons, List.prod_cons, Finset.prod_range_succ]
    rw [ih, mul_comm]

theorem masterPrimeHistory_auxiliary_eq {m : ℕ} (w e0 : ℕ) (M : ℕ+)
    (D : Finset (MvPolynomial (Fin m) ℤ)) (l : ℕ) :
    masterStageAuxiliary M (masterPrimeHistory w e0 M D l) = 2 + (M : ℕ) +
      ∏ j ∈ Finset.range l, (masterStageCutoff w e0 M D (masterPrimeHistory w e0 M D j)) ^ 2 := by
  rw [masterStageAuxiliary, masterPrimeHistory_cutoff_product]

theorem masterStagePool_lower_powerDominates {M : ℕ → ℕ+} {e0 : ℕ → ℕ}
    {history : ℕ → MasterPrimeHistory} :
    PowerDominates atTop (fun w => ((masterStagePool w (e0 w) (M w) (history w)).lower : ℝ))
      (fun w => (masterStageAuxiliary (M w) (history w) : ℝ)) :=
  equidistributedGrowingPrimePool_lower_powerDominates
    (fun w => masterStageModulus_pos w (e0 w) (masterStageAuxiliary (M w) (history w)))
    (Eventually.of_forall (fun w => masterStageAuxiliary_ge_one (M w) (history w)))

theorem masterStagePool_mass_powerDominates {M : ℕ → ℕ+} {e0 : ℕ → ℕ}
    {history : ℕ → MasterPrimeHistory} :
    PowerDominates atTop (fun w => (masterStagePool w (e0 w) (M w) (history w)).harmonicMass)
      (fun w => (masterStageAuxiliary (M w) (history w) : ℝ)) :=
  equidistributedGrowingPrimePool_mass_powerDominates
    (fun w => masterStageModulus_pos w (e0 w) (masterStageAuxiliary (M w) (history w)))
    (Eventually.of_forall (fun w => masterStageAuxiliary_ge_one (M w) (history w)))

theorem masterStagePool_atom_rapid {M : ℕ → ℕ+} {e0 p : ℕ → ℕ}
    {history : ℕ → MasterPrimeHistory} :
    RapidlySmall atTop (fun w => (masterStageAuxiliary (M w) (history w) : ℝ)) (fun w =>
      primePoolMass (masterStagePool w (e0 w) (M w) (history w)).lower
        (masterStagePool w (e0 w) (M w) (history w)).upper (p w)) :=
  equidistributedGrowingPrimePool_atom_rapid
    (fun w => masterStageModulus_pos w (e0 w) (masterStageAuxiliary (M w) (history w)))
    (Eventually.of_forall (fun w => masterStageAuxiliary_ge_one (M w) (history w)))

theorem masterStagePool_residue_rapid {M : ℕ → ℕ+} {e0 : ℕ → ℕ} {history : ℕ → MasterPrimeHistory} :
    RapidlySmall atTop (fun w => (masterStageAuxiliary (M w) (history w) : ℝ)) (fun w =>
      FiniteMass.distance (primePoolResidueMass
        (masterStageModulus w (e0 w) (masterStageAuxiliary (M w) (history w)))
        (masterStagePool w (e0 w) (M w) (history w)).lower
        (masterStagePool w (e0 w) (M w) (history w)).upper)
        (primeUnitUniformMass (masterStageModulus w (e0 w) (masterStageAuxiliary (M w) (history w))))) :=
  equidistributedGrowingPrimePool_residue_rapid
    (fun w => masterStageModulus_pos w (e0 w) (masterStageAuxiliary (M w) (history w)))
    (Eventually.of_forall (fun w => masterStageAuxiliary_ge_one (M w) (history w)))

theorem masterStageGap_powerDominates {m : ℕ} {M : ℕ → ℕ+} {e0 : ℕ → ℕ}
    {history : ℕ → MasterPrimeHistory} (D : Finset (MvPolynomial (Fin m) ℤ)) :
    PowerDominates atTop (fun w => (masterStageGap w (e0 w) (M w) D (history w) : ℝ))
      (fun w => ((masterStagePool w (e0 w) (M w) (history w)).upper +
        masterStageAuxiliary (M w) (history w) : ℕ)) := by
  apply powerDominates_of_parameter_power
  · apply Eventually.of_forall
    intro w
    have h := masterStageAuxiliary_ge_two (M w) (history w)
    exact_mod_cast (by omega : 1 ≤ (masterStagePool w (e0 w) (M w) (history w)).upper +
      masterStageAuxiliary (M w) (history w))
  · exact Eventually.of_forall (fun w => by exact_mod_cast masterStageGap_lower w (e0 w) (M w) D (history w))

theorem masterStageCutoff_powerDominates {m : ℕ} {M : ℕ → ℕ+} {e0 : ℕ → ℕ}
    {history : ℕ → MasterPrimeHistory} (D : Finset (MvPolynomial (Fin m) ℤ)) :
    PowerDominates atTop (fun w => Real.log (masterStageCutoff w (e0 w) (M w) D (history w)))
      (fun w => (masterStageGap w (e0 w) (M w) D (history w) : ℝ)) :=
  dyadicHarmonicCutoff_powerDominates (Eventually.of_forall
    (fun w => masterStageGap_pos w (e0 w) (M w) D (history w)))

end Hindman168
