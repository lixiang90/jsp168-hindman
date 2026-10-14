import Hindman168.NativeIndexExceptionalDensity
import Hindman168.RoughNaturalResidueIndexRange
import Hindman168.RoughIndexBadLaw

/-! Uniform original-source exceptional counts on actual residue intervals.
All raw sources, residues, moduli and signed endpoints follow the thresholds.
Only the original dyadic membership and interval length remain geometric inputs. -/
namespace Hindman168
open Filter
open scoped Classical
universe u

def NativeResidueExceptionalBound {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (n d w N₀ : ℕ) (Scale Z c C B η δ : ℝ) (L : NNReal) : Prop :=
  ∀ A B₀ : ℤ, 0 ≤ A → ∀ modulus r : ℕ, 0 < modulus →
    (∀ prime : ℕ, prime.Prime → prime ∣ modulus → prime ≤ w) →
    primorial w ∣ modulus → (primorial w).Coprime r →
    ∀ (Q : (Option (Fin n) → ℝ) → D.G)
      (p : RoughVectorMvPolynomial (Option (Fin n)) D.E),
    RoughVectorMvDegreeLE p d →
    (∀ (z : ℝ) (y : Fin n → ℝ), roughVectorMvEval p (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q (Option.elim · z y))) →
    (∀ t ∈ (alignmentIntervalClass A B₀ modulus r).image Int.toNat,
      Scale ≤ (t : ℝ) ∧ (t : ℝ) < 2*Scale) →
    N₀ ≤ ((alignmentIntervalClass A B₀ modulus r).image Int.toNat).card →
    ((((alignmentIntervalClass A B₀ modulus r).image Int.toNat).filter
      (fun t => RoughNativeBadIndex D Q t t Z c C L B η)).card : ℝ) <
      δ*(((alignmentIntervalClass A B₀ modulus r).image Int.toNat).card : ℝ)

theorem native_index_to_residue_exceptional_bound {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n d w N₀ : ℕ)
    (Scale Z c C B η δ : ℝ) (L : NNReal)
    (h : NativeIndexExceptionalBound D n d w N₀ Scale Z c C B η δ L) :
    NativeResidueExceptionalBound D n d w N₀ Scale Z c C B η δ L := by
  intro A B₀ hA modulus r hmod hsmooth hW hr Q p hp hlog hdyadic hlarge
  let N := (roughResidueCoordinateEndpoint B₀ modulus r-
    roughResidueCoordinateEndpoint A modulus r).toNat
  let t₀ := (alignmentResidueEndpoint A modulus r).toNat
  let f : ℕ → ℕ := fun j => t₀+modulus*j
  let Q' : (Option (Fin n) → ℝ) → D.G := fun x => Q
    (Option.elim · ((t₀ : ℝ)+(modulus : ℝ)*x none) (fun j => x (some j)))
  have himage : (Finset.range N).image f =
      (alignmentIntervalClass A B₀ modulus r).image Int.toNat :=
    rough_natural_residue_index_range_image A B₀ r modulus hmod hA
  have hcard : ((alignmentIntervalClass A B₀ modulus r).image Int.toNat).card=N :=
    rough_natural_residue_index_range_card A B₀ r modulus hmod hA
  have hinj : Function.Injective f := by
    intro j k he
    exact Nat.eq_of_mul_eq_mul_left hmod (Nat.add_left_cancel he)
  have hstart0 : 0 ≤ alignmentResidueEndpoint A modulus r :=
    hA.trans (alignmentResidueEndpoint_bounds A modulus r (by exact_mod_cast hmod)).1
  have hstart : Nat.ModEq modulus r t₀ := by
    apply Int.natCast_modEq_iff.mp
    rw [show (t₀ : ℤ)=alignmentResidueEndpoint A modulus r from Int.natCast_toNat_eq_self.mpr hstart0]
    exact (alignmentResidueEndpoint_modEq A modulus r).symm
  have hstartW := hstart.of_dvd hW
  have hcop (j : ℕ) : (primorial w).Coprime (f j) := by
    have he : Nat.ModEq (primorial w) r (f j) := by
      unfold Nat.ModEq at hstartW ⊢
      dsimp only [f]
      rw [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_zero_of_dvd hW,zero_mul,Nat.zero_mod,add_zero,Nat.mod_mod]
      exact hstartW
    change Nat.gcd (primorial w) (f j)=1
    rw [Nat.gcd_comm,← he.gcd_eq]
    exact hr.symm
  have hbound := h N t₀ modulus (by simpa only [hcard] using hlarge) Q'
    (roughParameterAffineSource (t₀ : ℝ) (modulus : ℝ) p)
    (rough_parameter_affine_degree _ _ hp) (by
      intro z y
      rw [rough_parameter_affine_eval]
      exact hlog _ y) hmod hsmooth (by
        intro j hj
        have hjT : f j ∈ (alignmentIntervalClass A B₀ modulus r).image Int.toNat := by
          rw [← himage]
          exact Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr hj,rfl⟩
        exact ⟨(hdyadic _ hjT).1,(hdyadic _ hjT).2,hcop j⟩)
  have heq : (((alignmentIntervalClass A B₀ modulus r).image Int.toNat).filter
      (fun t => RoughNativeBadIndex D Q t t Z c C L B η)).card =
      ((Finset.range N).filter (fun j => RoughNativeBadIndex D Q' j (f j) Z c C L B η)).card := by
    rw [← himage,Finset.filter_image,Finset.card_image_of_injective _ hinj]
    congr 1
    apply Finset.filter_congr
    intro j _hj
    exact (rough_index_bad_affine_iff D Q t₀ modulus j (f j) Z c C L B η).symm
  rw [heq,hcard]
  exact hbound

theorem native_residue_exceptional_density {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (n d : ℕ) (c C B η : ℝ) (L : NNReal)
    (hc : 0 < c) (hC : 1 ≤ C) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hScale : Tendsto Scale atTop atTop)
    (hg : ∀ a : ℝ, 0 < a → Tendsto (fun w => Z w/(Scale w)^a) atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ᶠ w in atTop,
      NativeResidueExceptionalBound D n d w N₀ (Scale w) (Z w) c C B η δ L := by
  obtain ⟨N₀,hN,hbound⟩ := native_index_exceptional_density D n d c C B η L
    hc hC hB hη Scale Z hScale hg hδ
  exact ⟨N₀,hN,hbound.mono (fun w hw =>
    native_index_to_residue_exceptional_bound D n d w N₀ _ _ _ _ _ _ _ L hw)⟩

end Hindman168
