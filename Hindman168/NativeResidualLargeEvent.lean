import Hindman168.NativeResidualSource
import Hindman168.RoughNestedResidueSampling
import Hindman168.RoughNativeComplexLargeIndex

/-! Original residual q/q*t discrepancy against arbitrary compatible finer
residues and actual boxes. Normalized geometry is the manuscript's condition.
There is NO gcd(q,t) premise. Retained a/q are external to the removed factor. -/
namespace Hindman168
open scoped Classical
universe u

def RoughNativeResidualComplexLargeIndex {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (a : κ → ℤ) (q z t : ℕ) (Z c C : ℝ) (L : NNReal) (B η : ℝ) : Prop :=
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  ∃ (lo hi b : κ → ℤ) (F : (D.G ⧸ D.Γ) → ℂ),
    LipschitzWith L F ∧ (∀ x, ‖F x‖ ≤ B) ∧
    (∀ j, c*Z ≤ (roughResidueBoxEndpoint hi a q j : ℝ)-roughResidueBoxEndpoint lo a q j ∧
      (roughResidueBoxEndpoint hi a q j : ℝ)-roughResidueBoxEndpoint lo a q j ≤ C*Z ∧
      |(roughResidueBoxEndpoint lo a q j : ℝ)| ≤ C*Z ∧
      |(roughResidueBoxEndpoint hi a q j : ℝ)| ≤ C*Z) ∧
    (∀ j, Int.ModEq q (a j) (b j)) ∧
    0 < (alignmentBoxClass lo hi b (q*t : ℕ)).card ∧
    0 < (alignmentBoxClass lo hi a q).card ∧
    η ≤ ‖FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass (alignmentBoxClass lo hi b (q*t : ℕ)))
        (fun y => F (QuotientGroup.mk (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))))))-
      FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass (alignmentBoxClass lo hi a q))
        (fun y => F (QuotientGroup.mk (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))))))‖

theorem rough_native_residual_large_event_normalize {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (a : κ → ℤ) (q z t : ℕ) (hq : 0 < q)
    (Z c C : ℝ) (L : NNReal) (B η : ℝ)
    (h : RoughNativeResidualComplexLargeIndex D Q a q z t Z c C L B η) :
    RoughNativeComplexLargeIndex D (roughNativeResidualSource D Q a q) z t Z c C L B η := by
  obtain ⟨lo,hi,b,F,hL,hB,hgeom,hcompatible,hfine,hcoarse,hlarge⟩ := h
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  obtain ⟨v,hrep,_hclasses⟩ := rough_nested_residue_compatible_representatives a b q t hqZ.ne' hcompatible
  have hb : b=(fun j => a j+(q : ℤ)*v j) := funext hrep
  rw [hb] at hfine hlarge
  simp only [Nat.cast_mul] at hfine hlarge
  have hfinecard := congrArg Finset.card (rough_nested_residue_box_image lo hi a v q t hqZ)
  rw [Finset.card_image_of_injective _ (rough_residue_box_affine_injective a q hqZ.ne')] at hfinecard
  have hcoarsecard := congrArg Finset.card (rough_residue_box_unrestricted_image lo hi a q hqZ)
  rw [Finset.card_image_of_injective _ (rough_residue_box_affine_injective a q hqZ.ne')] at hcoarsecard
  refine ⟨roughResidueBoxEndpoint lo a q,roughResidueBoxEndpoint hi a q,v,F,hL,hB,hgeom,
    by rw [hfinecard]; exact hfine,by rw [hcoarsecard]; exact hcoarse,?_⟩
  have he := rough_nested_residue_box_complex_discrepancy lo hi a v q t hqZ
    (fun y => F (QuotientGroup.mk (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))))))
  rw [he] at hlarge
  simpa only [roughNativeResidualSource,roughResidueBoxAffine,Option.elim_none,Option.elim_some,
    Int.cast_add,Int.cast_mul,Int.cast_natCast] using hlarge

end Hindman168
