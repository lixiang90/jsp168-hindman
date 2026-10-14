import Hindman168.RoughNaturalResidueIndexRange
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.ModEq

/-! The actual original dyadic residue set, exact ceil endpoints, and a
uniform length lower bound from S/modulus. No assumed dense interval. -/
namespace Hindman168
open scoped Classical

noncomputable def roughDyadicResidueSteps (S : ℝ) (modulus r : ℕ) : Finset ℕ :=
  (alignmentIntervalClass ⌈S⌉ ⌈2*S⌉ modulus r).image Int.toNat

theorem rough_dyadic_residue_steps_mem {S : ℝ} (hS : 0 ≤ S) (modulus r t : ℕ) :
    t ∈ roughDyadicResidueSteps S modulus r ↔
      S ≤ (t : ℝ) ∧ (t : ℝ) < 2*S ∧ Nat.ModEq modulus r t := by
  constructor
  · intro ht
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp ht
    obtain ⟨hxAB,hxmod⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxA,hxB⟩ := Finset.mem_Ico.mp hxAB
    have hx0 : 0 ≤ x := (Int.ceil_nonneg hS).trans hxA
    have htX : (t : ℤ)=x := by rw [←he,Int.natCast_toNat_eq_self.mpr hx0]
    have hlo : S ≤ (t : ℝ) := by
      have hxa : (⌈S⌉ : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxA
      have hxt : (t : ℝ)=(x : ℝ) := by exact_mod_cast htX
      rw [hxt]
      exact (Int.le_ceil S).trans hxa
    have hhi : (t : ℝ) < 2*S := by
      have hxt : (t : ℝ)=(x : ℝ) := by exact_mod_cast htX
      rw [hxt]
      exact Int.lt_ceil.mp hxB
    exact ⟨hlo,hhi,Int.natCast_modEq_iff.mp (by rw [htX]; exact hxmod)⟩
  · rintro ⟨hlo,hhi,hmod⟩
    apply Finset.mem_image.mpr
    refine ⟨(t : ℤ),Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ?_,?_⟩,by simp⟩
    · exact ⟨Int.ceil_le.mpr hlo,Int.lt_ceil.mpr hhi⟩
    · exact Int.natCast_modEq_iff.mpr hmod

theorem rough_dyadic_residue_steps_card_lower (S : ℝ) (hS : 0 ≤ S)
    (modulus r N₀ : ℕ) (hmod : 0 < modulus)
    (hratio : (N₀ : ℝ)+2 ≤ S/(modulus : ℝ)) :
    N₀ ≤ (roughDyadicResidueSteps S modulus r).card := by
  have hmodZ : (0 : ℤ) < modulus := by exact_mod_cast hmod
  have hmodR : (0 : ℝ) < modulus := by exact_mod_cast hmod
  have hmod1 : (1 : ℝ) ≤ modulus := by exact_mod_cast hmod
  have hAB : ⌈S⌉ ≤ ⌈2*S⌉ := Int.ceil_mono (by linarith)
  have heps := rough_residue_coordinate_endpoint_mono modulus r hmodZ hAB
  have hlen0 : 0 ≤ roughResidueCoordinateEndpoint ⌈2*S⌉ modulus r-
      roughResidueCoordinateEndpoint ⌈S⌉ modulus r := sub_nonneg.mpr heps
  have hcard : ((roughDyadicResidueSteps S modulus r).card : ℝ) =
      (roughResidueCoordinateEndpoint ⌈2*S⌉ modulus r : ℝ)-
      roughResidueCoordinateEndpoint ⌈S⌉ modulus r := by
    rw [roughDyadicResidueSteps,rough_natural_residue_index_range_card _ _ _ _ hmod (Int.ceil_nonneg hS)]
    exact_mod_cast Int.natCast_toNat_eq_self.mpr hlen0
  have he := (abs_lt.mp (rough_residue_coordinate_length_error ⌈S⌉ ⌈2*S⌉ modulus r hmodZ)).1
  push_cast at he
  have hupper := Int.ceil_lt_add_one S
  have hlower := Int.le_ceil (2*S)
  have hratio' := (le_div_iff₀ hmodR).mp hratio
  have hcount : (N₀ : ℝ) ≤ (roughDyadicResidueSteps S modulus r).card := by
    rw [hcard]
    have hprod : (modulus : ℝ)*(N₀ : ℝ) <
        (modulus : ℝ)*((roughResidueCoordinateEndpoint ⌈2*S⌉ modulus r : ℝ)-
          roughResidueCoordinateEndpoint ⌈S⌉ modulus r) := by nlinarith
    exact (lt_of_mul_lt_mul_left hprod hmodR.le).le
  exact_mod_cast hcount

end Hindman168
