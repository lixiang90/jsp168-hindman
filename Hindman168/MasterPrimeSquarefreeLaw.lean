import Hindman168.FinitePushContraction
import Hindman168.MasterParameterFamily
import Hindman168.FiniteMasterSelection

/-!
# Actual independent master prime slots at squarefree CRT moduli

Only the first power of each rough prime is needed for the polynomial
beta test. Each slot uses a fresh draw, even when gap labels repeat.
Projection from the actual master residue modulus and product L1
contraction give a uniform joint law and every inverse-power error rate.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

abbrev squarefreeCRTModulus (S : Finset ℕ) : ℕ := ∏ p : S, (p : ℕ)

theorem squarefreeCRTModulus_ne_zero (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    squarefreeCRTModulus S ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun p _ => (hS p p.property).ne_zero)

noncomputable def squarefreeCRTUniformParameterMass (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (r : ℕ) : Mass (Fin r → ZMod (squarefreeCRTModulus S)) :=
  letI : NeZero (squarefreeCRTModulus S) := ⟨squarefreeCRTModulus_ne_zero S hS⟩
  piMass (fun _ : Fin r => zmodUnitUniformMass (squarefreeCRTModulus S))

theorem primeUnitUniformMass_quotient_cast {Q R : ℕ} [NeZero Q] [NeZero R] (h : R ∣ Q) :
    (primeUnitUniformMass Q).mapDomain (fun a : ℕ => (a : ZMod R)) = zmodUnitUniformMass R := by
  have hf : (fun a : ℕ => (a : ZMod R)) =
      (ZMod.castHom h (ZMod R)) ∘ (fun a : ℕ => (a : ZMod Q)) := by
    funext a
    simp
  rw [hf, Finsupp.mapDomain_comp, primeUnitUniformMass_cast, zmodUnitUniformMass_quotient h]

theorem primePoolMass_quotient_cast_bound {Q R : ℕ} [NeZero Q] [NeZero R]
    (h : R ∣ Q) (A B : ℕ) :
    distance ((primePoolMass A B).mapDomain (fun a : ℕ => (a : ZMod R)))
      (zmodUnitUniformMass R) ≤ distance (primePoolResidueMass Q A B) (primeUnitUniformMass Q) := by
  have hm : (primePoolMass A B).mapDomain (fun a : ℕ => (a : ZMod R)) =
      (primePoolResidueMass Q A B).mapDomain (fun a : ℕ => (a : ZMod R)) := by
    rw [primePoolResidueMass, ← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr (fun a _ => (natCast_mod_divisor h a).symm)
  rw [hm, ← primeUnitUniformMass_quotient_cast h]
  exact distance_push_le _ _ _

theorem squarefreeCRTModulus_dvd_masterStage (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (w e V : ℕ) (hgreater : ∀ p ∈ S, w < p) (hV : ∀ p ∈ S, p ≤ V) :
    squarefreeCRTModulus S ∣ masterStageModulus w e V := by
  change (∏ p : S, (p : ℕ)) ∣ _
  rw [Finset.prod_coe_sort S (fun p => p)]
  have hs : S ⊆ (Finset.Icc (w + 1) V).filter Nat.Prime := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by have h := hgreater p hp; omega, hV p hp⟩, hS p hp⟩
  exact (Finset.prod_dvd_prod_of_subset S _ (fun p => p) hs).trans (dvd_mul_left _ _)

noncomputable def masterPrimeSlotsMass {r : ℕ} (F : MasterParameterFamily) (w : ℕ)
    (gap : Fin r → ℕ) : Mass (Fin r → ℕ) :=
  piMass (fun j => primePoolMass (F.pool w (gap j)).lower (F.pool w (gap j)).upper)

noncomputable def masterPrimeSlotsResidueError {r : ℕ} (F : MasterParameterFamily) (w : ℕ)
    (gap : Fin r → ℕ) : ℝ :=
  ∑ j, distance (primePoolResidueMass (F.residueModulus w (gap j))
    (F.pool w (gap j)).lower (F.pool w (gap j)).upper)
      (primeUnitUniformMass (F.residueModulus w (gap j)))

theorem masterPrimeSlotsResidueError_nonneg {r : ℕ} (F : MasterParameterFamily) (w : ℕ)
    (gap : Fin r → ℕ) : 0 ≤ masterPrimeSlotsResidueError F w gap :=
  Finset.sum_nonneg (fun _ _ => distance_nonneg _ _)

theorem MasterParameterConditions.prime_slots_nonneg {n N r : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (_hF : MasterParameterConditions N A D F) (w : ℕ) (gap : Fin r → ℕ) (x : Fin r → ℕ) :
    0 ≤ masterPrimeSlotsMass F w gap x :=
  piMass_nonneg _ (fun _j => primePoolMass_nonneg _ _) x

theorem MasterParameterConditions.prime_slots_total {n N r : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (w : ℕ) (gap : Fin r → ℕ) :
    total (masterPrimeSlotsMass F w gap) = 1 :=
  piMass_total_one _ (fun j => primePoolMass_total (hF.pool_positive_mass w (gap j)))

theorem MasterParameterConditions.prime_slots_squarefree_bound {n N r : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (w : ℕ) (gap : Fin r → ℕ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hgreater : ∀ p ∈ S, w < p)
    (hbudget : ∀ j, ∀ p ∈ S, p ≤ F.auxiliary w (gap j)) :
    distance ((masterPrimeSlotsMass F w gap).mapDomain
      (fun (x : Fin r → ℕ) j => (x j : ZMod (squarefreeCRTModulus S))))
        (squarefreeCRTUniformParameterMass S hS r) ≤ masterPrimeSlotsResidueError F w gap := by
  letI : NeZero (squarefreeCRTModulus S) := ⟨squarefreeCRTModulus_ne_zero S hS⟩
  rw [masterPrimeSlotsMass, piMass_map, squarefreeCRTUniformParameterMass]
  apply (piMass_probability_distance_sum r _ _
    (fun j => push_nonneg _ _ (primePoolMass_nonneg _ _))
    (fun _ => zmodUnitUniformMass_nonneg _)
    (fun j => by rw [total_push]; exact primePoolMass_total (hF.pool_positive_mass w (gap j)))
    (fun _ => zmodUnitUniformMass_total _)).trans
  apply Finset.sum_le_sum
  intro j hj
  letI : NeZero (masterStageModulus w (F.exponent w) (F.auxiliary w (gap j))) :=
    ⟨(masterStageModulus_pos _ _ _).ne'⟩
  exact primePoolMass_quotient_cast_bound
    (squarefreeCRTModulus_dvd_masterStage S hS w (F.exponent w) _ hgreater (hbudget j)) _ _

theorem MasterParameterConditions.prime_slots_residue_rapid {n N r L : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap : ℕ → Fin r → Fin L) {V : ℕ → ℕ}
    (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hbudget : ∀ᶠ w in atTop, ∀ j, V w ≤ F.auxiliary w (gap w j)) :
    RapidlySmall atTop (fun w => (V w : ℝ))
      (fun w => masterPrimeSlotsResidueError F w (fun j => gap w j)) := by
  apply RapidlySmall.finset_sum Finset.univ
  intro j hj
  apply RapidlySmall.finite_choice (fun i : Fin L => hF.pool_residue_error i) (fun w => gap w j)
  · exact hV.mono (fun _ hw => by exact_mod_cast (by omega : 0 < V _))
  · exact hbudget.mono (fun _ hw => by exact_mod_cast hw j)

theorem MasterParameterConditions.prime_slots_squarefree_rapid {n N r L : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap : ℕ → Fin r → Fin L) {V : ℕ → ℕ}
    (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hbudget : ∀ᶠ w in atTop, ∀ j, V w ≤ F.auxiliary w (gap w j))
    (S : ℕ → Finset ℕ) (hS : ∀ w, ∀ p ∈ S w, p.Prime)
    (hgreater : ∀ w, ∀ p ∈ S w, w < p) (hbound : ∀ w, ∀ p ∈ S w, p ≤ V w) :
    RapidlySmall atTop (fun w => (V w : ℝ)) (fun w =>
      distance ((masterPrimeSlotsMass F w (fun j => gap w j)).mapDomain
        (fun (x : Fin r → ℕ) j => (x j : ZMod (squarefreeCRTModulus (S w)))))
          (squarefreeCRTUniformParameterMass (S w) (hS w) r)) := by
  apply (hF.prime_slots_residue_rapid gap hV hbudget).of_abs_le
  filter_upwards [hbudget] with w hw
  rw [abs_of_nonneg (distance_nonneg _ _), abs_of_nonneg (masterPrimeSlotsResidueError_nonneg _ _ _)]
  exact hF.prime_slots_squarefree_bound w _ (S w) (hS w) (hgreater w)
    (fun j p hp => (hbound w p hp).trans (hw j))

theorem MasterParameterConditions.prime_slots_weighted_error_tendsto_zero {n N r L : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (gap : ℕ → Fin r → Fin L) {V : ℕ → ℕ}
    (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hbudget : ∀ᶠ w in atTop, ∀ j, V w ≤ F.auxiliary w (gap w j)) (q : ℕ) :
    Tendsto (fun w => (V w : ℝ) ^ q * masterPrimeSlotsResidueError F w (fun j => gap w j))
      atTop (𝓝 0) := by
  apply (Asymptotics.isLittleO_one_iff ℝ).mp
  simpa only [pow_zero, inv_one] using
    ((hF.prime_slots_residue_rapid gap hV hbudget).mul_power
      (hV.mono (fun _ hw => by exact_mod_cast (by omega : 0 < V _))) q) 0

end Hindman168
