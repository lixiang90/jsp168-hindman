import Hindman168.RoughNativeBadFamily

namespace Hindman168
open Filter
open scoped Classical
universe u

/-- Fixed finite choices may have different periods and quantitative bounds.
After cofinal selection all of them are fixed at the selected index. -/
theorem rough_native_finite_bad_data_subsequences {κ ι : Type*}
    [Fintype κ] [Fintype ι] {step : ℕ}
    (D : NativeNilmanifoldData.{u} step) (family : ι → NativeNilmanifoldData.{u} step)
    (hdim : ∀ i, Module.finrank ℝ (family i).E < Module.finrank ℝ D.E)
    (Scale Z : ℕ → ℝ) (K : ι → ℝ) (hK : ∀ i, 0 < K i)
    (hg : PowerDominates atTop Z Scale) (hScale : Tendsto Scale atTop atTop)
    (d : ι → ℕ) (c C : ι → ℝ) (L : ι → NNReal) (B η : ι → ℝ)
    (h : ∀ H0 w0 : ℕ, ∃ (i : ι) (H w : ℕ), H0 ≤ H ∧ w0 ≤ w ∧
      RoughNativeBadFamily (κ := κ) (family i) H w (Scale w) (Z w/K i)
        (d i) (c i) (C i) (L i) (B i) (η i)) :
    ∃ i : ι, Module.finrank ℝ (family i).E < Module.finrank ℝ D.E ∧
      ∀ H : ℕ, ∃ f : ℕ → ℕ, StrictMono f ∧
        Tendsto (fun n => Scale (f n)) atTop atTop ∧
        PowerDominates atTop (fun n => Z (f n)/K i) (fun n => Scale (f n)) ∧
        ∀ n, RoughNativeBadFamily (κ := κ) (family i) H (f n)
          (Scale (f n)) (Z (f n)/K i) (d i) (c i) (C i) (L i) (B i) (η i) := by
  let P := fun i H w => RoughNativeBadFamily (κ := κ) (family i) H w (Scale w)
    (Z w/K i) (d i) (c i) (C i) (L i) (B i) (η i)
  obtain ⟨i, hi⟩ := rough_finite_lengthwise_subsequences P
    (fun i _ _ _ hh hp => rough_native_bad_family_length_mono (family i) hh hp) h
  refine ⟨i, hdim i, ?_⟩
  intro H
  obtain ⟨f, hf, hp⟩ := hi H
  exact ⟨f, hf, hScale.comp hf.tendsto_atTop,
    rough_subsequence_rescaled_growth hg (K i) (hK i) f hf, hp⟩

end Hindman168
