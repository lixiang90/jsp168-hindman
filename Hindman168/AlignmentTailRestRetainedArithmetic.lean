import Hindman168.AlignmentTailRestWindowGeometry
import Hindman168.AlignmentRetainedCubeResidue

/-! Actual rest-window values inherit rough units from the original raw
anchor. Retained q and CRT residues are constructed on the supported rest
fiber and remain fixed when its removed factor varies. -/
namespace Hindman168
open FiniteMass
open scoped Classical BigOperators

theorem alignment_native_window_value_coprime {N k : ℕ} {A : Finset ℚ}
    {P : Finset (MvPolynomial (Fin k) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A P F) (w : ℕ) (hw : 1 ≤ w)
    (x : Fin N → ℕ) (hx : x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support)
    (j : Fin N) (t : ℕ)
    (ht : t ∈ binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x j)) :
    Nat.Coprime t (primorial w) := by
  have har := alignment_native_window_arithmetic hF w hw x hx j
  have hres := ((binaryDyadicResidueWindow_mem (alignment_window_value_positive ht)).mp ht).2
  exact (residue_coprime_iff (primorial w) ((F.modulus w : ℕ)*(primorial w)^w)
    (x j % ((F.modulus w : ℕ)*(primorial w)^w)) t har.2.2.1 hres).mpr har.2.2.2.symm

theorem alignment_tail_rest_retained_arithmetic {N k : ℕ} {A : Finset ℚ}
    {P : Finset (MvPolynomial (Fin k) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A P F) (w d : ℕ) (hd : 0 < d) (hw : d ≤ w)
    (hw₁ : 1 ≤ w) (T U : Finset (Fin N)) (hU : U ⊆ T)
    (x : Fin N → ℕ) (hx : x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support)
    (j : T) (rest : {k : T // k ≠ j} → ℕ)
    (hrest : rest ∈ (piMass (fun k : {k : T // k ≠ j} => uniformFinsetMass
      (binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x k.val.val)))).support) :
    let y := alignmentTailTuple T x (insertPivotCoordinate j rest (x j.val))
    0 < alignmentNaturalBlockProduct y U ∧
      Nat.Coprime (F.modulus w : ℕ) (alignmentNaturalBlockProduct y U) ∧
      Nat.Coprime d (alignmentNaturalBlockProduct y U) := by
  dsimp only
  have hwin := alignment_tail_rest_all_windows T x _ j rest hrest (x j.val)
    (binaryDyadicResidueWindow_anchor (alignmentGlobalRawMass_support_positive hF w x hx j.val))
  refine ⟨Finset.prod_pos (fun k hk => alignment_window_value_positive (hwin k (hU hk))),?_⟩
  exact alignmentMaster_retained_coprime hF w d hd hw _ U
    (fun k hk => alignment_native_window_value_coprime hF w hw₁ x hx k _ (hwin k (hU hk)))

theorem alignment_tail_rest_cube_residue_fixed {N : ℕ} {κ : Type*}
    (T U : Finset (Fin N)) (x : Fin N → ℕ) (j : T) (hj : j.val ∉ U)
    (rest : {k : T // k ≠ j} → ℕ) (z t M d : ℕ) (Y r : ℤ) (c : Option κ → ℤ) :
    alignmentRetainedCubeResidue M d
      (alignmentNaturalBlockProduct (alignmentTailTuple T x (insertPivotCoordinate j rest t)) U) Y r c =
    alignmentRetainedCubeResidue M d
      (alignmentNaturalBlockProduct (alignmentTailTuple T x (insertPivotCoordinate j rest z)) U) Y r c := by
  rw [alignment_tail_rest_retained_product T U x j hj rest z t]

end Hindman168
