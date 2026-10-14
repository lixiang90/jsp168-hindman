import Hindman168.RoughNativeBadIndex
import Hindman168.RoughVectorMvPolynomial
import Hindman168.RoughCofinalSubsequences
import Hindman168.MasterScales

namespace Hindman168
open scoped Classical
open Filter
universe u

/-- A finite bad progression on the actual quotient, with one joint native
logarithmic polynomial and varying bounded tests and boxes. -/
def RoughNativeBadFamily {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H w : ℕ) (Scale Z : ℝ)
    (d : ℕ) (c C : ℝ) (L : NNReal) (B η : ℝ) : Prop :=
  ∃ (Q : (Option κ → ℝ) → D.G) (p : RoughVectorMvPolynomial (Option κ) D.E)
    (t diff : ℕ),
    RoughVectorMvDegreeLE p d ∧
    (∀ (z : ℝ) (y : κ → ℝ), roughVectorMvEval p (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q (Option.elim · z y))) ∧
    0 < diff ∧ (∀ prime : ℕ, prime.Prime → prime ∣ diff → prime ≤ w) ∧
    ∀ z : ℕ, z < H → Scale ≤ (t+diff*z : ℕ) ∧ (t+diff*z : ℕ) < 2*Scale ∧
      (primorial w).Coprime (t+diff*z) ∧
      RoughNativeBadIndex D Q z (t+diff*z) Z c C L B η

theorem rough_native_bad_family_length_mono {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) {H H' w : ℕ} {Scale Z : ℝ}
    {d : ℕ} {c C : ℝ} {L : NNReal} {B η : ℝ} (hH : H ≤ H')
    (h : RoughNativeBadFamily (κ := κ) D H' w Scale Z d c C L B η) :
    RoughNativeBadFamily (κ := κ) D H w Scale Z d c C L B η := by
  obtain ⟨Q, p, t, diff, hd, hp, hdiff, hsmooth, hbad⟩ := h
  exact ⟨Q, p, t, diff, hd, hp, hdiff, hsmooth, fun z hz => hbad z (hz.trans_le hH)⟩

/-- The same actual quotient works at every fixed length on a genuine
increasing scale subsequence. Only the choice of subsequence depends on H. -/
theorem rough_native_fixed_bad_quotient_subsequences {κ ι : Type*}
    [Fintype κ] [Fintype ι] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (family : ι → NativeNilmanifoldData.{u} s)
    (hdim : ∀ j, Module.finrank ℝ (family j).E < Module.finrank ℝ D.E)
    (Scale Z : ℕ → ℝ) (K : ℝ) (hK : 0 < K)
    (hg : PowerDominates atTop Z Scale) (hScale : Tendsto Scale atTop atTop)
    (d : ℕ) (c C : ℝ) (L : NNReal) (B η : ℝ)
    (h : ∀ H0 w0 : ℕ, ∃ (j : ι) (H w : ℕ), H0 ≤ H ∧ w0 ≤ w ∧
      RoughNativeBadFamily (κ := κ) (family j) H w (Scale w) (Z w/K) d c C L B η) :
    ∃ j : ι, Module.finrank ℝ (family j).E < Module.finrank ℝ D.E ∧
      ∀ H : ℕ, ∃ f : ℕ → ℕ, StrictMono f ∧
        Tendsto (fun n => Scale (f n)) atTop atTop ∧
        PowerDominates atTop (fun n => Z (f n)/K) (fun n => Scale (f n)) ∧
        ∀ n, RoughNativeBadFamily (κ := κ) (family j) H (f n)
          (Scale (f n)) (Z (f n)/K) d c C L B η := by
  let P := fun j H w => RoughNativeBadFamily (κ := κ) (family j) H w
    (Scale w) (Z w/K) d c C L B η
  obtain ⟨j, hj⟩ := rough_finite_lengthwise_subsequences P
    (fun j _ _ _ hh hp => rough_native_bad_family_length_mono (family j) hh hp) h
  refine ⟨j, hdim j, ?_⟩
  intro H
  obtain ⟨f, hf, hp⟩ := hj H
  exact ⟨f, hf, hScale.comp hf.tendsto_atTop,
    rough_subsequence_rescaled_growth hg K hK f hf, hp⟩

end Hindman168
