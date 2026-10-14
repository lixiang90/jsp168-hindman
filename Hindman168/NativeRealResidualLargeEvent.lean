import Hindman168.ResidualRealBoxGeometry
import Hindman168.NativeResidualLargeEvent

/-! ORIGINAL arbitrary real spatial boxes. Actual ceil samples carry the
original q/q*t laws; no assumed nonempty event is inserted into this definition.
The sampling thresholds prove nonemptiness simultaneously for all such boxes. -/
namespace Hindman168
open Filter
open scoped Classical
universe u

def RoughNativeRealResidualComplexLargeIndex {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (a : κ → ℤ) (q z t : ℕ) (Z c C : ℝ) (L : NNReal) (B η : ℝ) : Prop :=
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  ∃ (lo hi : κ → ℝ) (b : κ → ℤ) (F : (D.G ⧸ D.Γ) → ℂ),
    LipschitzWith L F ∧ (∀ x, ‖F x‖ ≤ B) ∧
    (∀ j, c*Z ≤ (hi j-(a j : ℝ))/(q : ℝ)-(lo j-(a j : ℝ))/(q : ℝ) ∧
      (hi j-(a j : ℝ))/(q : ℝ)-(lo j-(a j : ℝ))/(q : ℝ) ≤ C*Z ∧
      |(lo j-(a j : ℝ))/(q : ℝ)| ≤ C*Z ∧ |(hi j-(a j : ℝ))/(q : ℝ)| ≤ C*Z) ∧
    (∀ j, Int.ModEq q (a j) (b j)) ∧
    η ≤ ‖FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass
        (alignmentBoxClass (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) b (q*t : ℕ)))
        (fun y => F (QuotientGroup.mk (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))))))-
      FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass
        (alignmentBoxClass (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) a q))
        (fun y => F (QuotientGroup.mk (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))))))‖

theorem rough_native_real_residual_event_integer {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (a : κ → ℤ) (q z t : ℕ) (hq : 0 < q) (ht : 0 < t)
    (Z c C : ℝ) (L : NNReal) (B η : ℝ) (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (hlarge : 2 ≤ c*Z) (hstep : 4*(t : ℝ) ≤ c*Z)
    (h : RoughNativeRealResidualComplexLargeIndex D Q a q z t Z c C L B η) :
    RoughNativeResidualComplexLargeIndex D Q a q z t Z (c/2) (2*(C+1)) L B η := by
  obtain ⟨lo,hi,b,F,hL,hB,hgeom,hcompatible,hdiscrepancy⟩ := h
  have hgeometry := rough_residual_real_box_integer_geometry lo hi a q hq Z c C hZ hC hlarge hgeom
  have hnonempty := rough_residual_real_box_samples_nonempty lo hi a b q t hq ht
    Z c C hZ hC hlarge hstep hgeom hcompatible
  exact ⟨(fun j => ⌈lo j⌉),(fun j => ⌈hi j⌉),b,F,hL,hB,hgeometry,hcompatible,
    hnonempty.2,hnonempty.1,hdiscrepancy⟩

theorem rough_real_residual_sampling_thresholds (c : ℝ) (hc : 0 < c)
    (Scale Z : ℕ → ℝ) (hScale : Tendsto Scale atTop atTop)
    (hg : ∀ e : ℝ, 0 < e → Tendsto (fun w => Z w/(Scale w)^e) atTop atTop) :
    ∀ᶠ w in atTop, 1 ≤ Scale w ∧ 1 ≤ Z w ∧ 2 ≤ c*Z w ∧
      ∀ t : ℕ, Scale w ≤ (t : ℝ) → (t : ℝ) < 2*Scale w →
        0 < t ∧ 4*(t : ℝ) ≤ c*Z w := by
  let A := max 1 (8/c)
  filter_upwards [hScale.eventually (eventually_ge_atTop 1),
    (hg 1 (by norm_num)).eventually (eventually_ge_atTop A)] with w hS hratio
  have hSp : 0 < Scale w := zero_lt_one.trans_le hS
  have hratio' : A ≤ Z w/Scale w := by simpa only [Real.rpow_one] using hratio
  have hAZ := (le_div_iff₀ hSp).mp hratio'
  have hSZ : Scale w ≤ A*Scale w := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 (8/c)) hSp.le
  have hZ : 1 ≤ Z w := hS.trans (hSZ.trans hAZ)
  have hcz : (8/c)*Scale w ≤ Z w :=
    (mul_le_mul_of_nonneg_right (le_max_right 1 (8/c)) hSp.le).trans hAZ
  have hcZ : 8*Scale w ≤ c*Z w := by
    have hh := mul_le_mul_of_nonneg_left hcz hc.le
    have he : c*((8/c)*Scale w)=8*Scale w := by field_simp
    rw [he] at hh
    exact hh
  refine ⟨hS,hZ,by nlinarith,?_⟩
  intro t hlo hhi
  have htR : (0 : ℝ) < t := hSp.trans_le hlo
  exact ⟨by exact_mod_cast htR,by nlinarith⟩

end Hindman168
