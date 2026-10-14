import Hindman168.NativeRealResidualRoughProportion

/-! The original arbitrary REAL-box rough-step event is residual removal
with retained step one and zero residue. Coarse samples are exactly the full
integer points of the real box. No nonempty-sample premise is added. -/
namespace Hindman168
open Filter
open scoped Classical Topology
universe u

def RoughNativeRealComplexLargeIndex {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (z t : ℕ) (Z c C : ℝ) (L : NNReal) (B η : ℝ) : Prop :=
  RoughNativeRealResidualComplexLargeIndex D Q (fun _ => 0) 1 z t Z c C L B η

theorem rough_real_box_unit_class {κ : Type*} [Fintype κ] (lo hi : κ → ℝ) :
    alignmentBoxClass (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) (fun _ => 0) 1 =
      roughRealIntegerBox lo hi := by
  simp [alignmentBoxClass,alignmentIntervalClass,roughRealIntegerBox,Int.ModEq]

theorem rough_native_residual_identity_source {κ : Type*} {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G) :
    roughNativeResidualSource D Q (fun _ => 0) 1=Q := by
  funext x
  unfold roughNativeResidualSource
  apply congrArg Q
  funext i
  cases i <;> simp

theorem native_finite_real_original_rough_fraction_tendsto {s : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s) (index : ℕ → ι)
    (n d : ℕ) (c C B η : ℝ) (L : NNReal) (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hScale : Tendsto Scale atTop atTop)
    (hg : ∀ e : ℝ, 0 < e → Tendsto (fun w => Z w/(Scale w)^e) atTop atTop)
    (modulus r : ℕ → ℕ)
    (hm : ∀ᶠ w in atTop, 0 < modulus w)
    (hs : ∀ᶠ w in atTop, ∀ prime : ℕ, prime.Prime → prime ∣ modulus w → prime ≤ w)
    (hW : ∀ᶠ w in atTop, primorial w ∣ modulus w)
    (hr : ∀ᶠ w in atTop, (primorial w).Coprime (r w))
    (hratio : Tendsto (fun w => Scale w/(modulus w : ℝ)) atTop atTop)
    (Q : ∀ w, (Option (Fin n) → ℝ) → (D (index w)).G)
    (p : ∀ w, RoughVectorMvPolynomial (Option (Fin n)) (D (index w)).E)
    (hp : ∀ w, RoughVectorMvDegreeLE (p w) d)
    (hlog : ∀ w (z : ℝ) (y : Fin n → ℝ), roughVectorMvEval (p w) (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := (D (index w)).E) (I := (D (index w)).I)
        (Q w (Option.elim · z y))) :
    Tendsto (fun w =>
      (((roughDyadicResidueSteps (Scale w) (modulus w) (r w)).filter
        (fun t => RoughNativeRealComplexLargeIndex (D (index w)) (Q w) t t (Z w) c C L B η)).card : ℝ)/
      ((roughDyadicResidueSteps (Scale w) (modulus w) (r w)).card : ℝ)) atTop (𝓝 0) := by
  apply native_finite_real_residual_rough_fraction_tendsto D index n d c C B η L
    hc hC hB hη Scale Z hScale hg modulus r (fun _ => 1) (fun _ _ => 0)
    hm (Eventually.of_forall (fun _ => Nat.zero_lt_one)) hs hW hr hratio Q p hp
  intro w z y
  rw [rough_native_residual_identity_source]
  exact hlog w z y

end Hindman168
