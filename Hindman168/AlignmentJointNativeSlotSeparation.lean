import Hindman168.AlignmentJointNativeReadings

/-! ALL original integer-slot quotient readings determine the ACTUAL native
array/product quotient. This uses the genuine pointwise/product lattice,
not an unproved finite-evaluation lattice-quotient embedding. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

variable {ι : Type} [Fintype ι] {σ : ι → Type} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → σ ν → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

theorem alignment_array_native_lattice_iff {τ : Type} {step : ℕ}
    (data : NativeNilmanifoldData.{u} step) (degree : ℕ) (evaluations : Fin (degree+1) → τ → ℤ)
    (injective : Function.Injective (alignmentNativeFiniteEvaluation (E := data.E) (I := data.I) (G := data.G) degree evaluations))
    (a : (alignmentNativeArrayData data degree evaluations injective).G) :
    a ∈ (alignmentNativeArrayData data degree evaluations injective).Γ ↔
      ∀ z : τ → ℤ, alignmentArrayNativeEvaluation data degree evaluations injective z a ∈ data.Γ := by
  let raw : alignmentNativeAllIntegerArrayGroup (E := data.E) (I := data.I) (G := data.G) degree evaluations injective := a
  change raw ∈ pointwiseArrayLattice _ data.Γ ↔ ∀ z, raw.val z ∈ data.Γ
  exact pointwiseArrayLattice_mem _ data.Γ raw

theorem alignment_joint_native_all_slot_readings_eq_iff
    (x y : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ) :
    (∀ ν (z : σ ν → ℤ), alignmentJointNativeCosetEvaluation D n v hv ν z x=
      alignmentJointNativeCosetEvaluation D n v hv ν z y) ↔ x=y := by
  constructor
  · intro h
    induction x,y using Quotient.inductionOn₂ with
    | _ a b =>
      apply QuotientGroup.eq.mpr
      apply (native_finite_pi_lattice_mem (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) (a⁻¹*b)).mpr
      intro ν
      apply (alignment_array_native_lattice_iff (D ν) (n ν) (v ν) (hv ν) _).mpr
      intro z
      simp only [map_mul,map_inv,Pi.mul_apply,Pi.inv_apply]
      exact QuotientGroup.eq.mp (h ν z)
  · intro h ν z
    exact congrArg (alignmentJointNativeCosetEvaluation D n v hv ν z) h

theorem alignment_joint_native_distinct_slot_witness
    (x y : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ)
    (hxy : x ≠ y) :
    ∃ (ν : ι) (z : σ ν → ℤ), alignmentJointNativeCosetEvaluation D n v hv ν z x ≠
      alignmentJointNativeCosetEvaluation D n v hv ν z y := by
  by_contra hn
  apply hxy
  apply (alignment_joint_native_all_slot_readings_eq_iff D n v hv x y).mp
  intro ν z
  by_contra hz
  exact hn ⟨ν,z,hz⟩

end Hindman168
