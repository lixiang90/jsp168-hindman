import Hindman168.RoughHorizontalError

namespace Hindman168
open Polynomial Filter
open scoped Topology BigOperators

theorem rough_horizontal_interpolation_step
    {α ι : Type*} {l : Filter α} {W : α → ℕ} (hW : Tendsto W l atTop)
    {S Z : α → ℝ} (hg : PowerDominates l Z S)
    (hS : ∀ᶠ w in l, 1 ≤ S w) (hZ : ∀ᶠ w in l, 0 < Z w)
    (e q H : ℕ) (he : 0 < e) (heq : e ≤ q) (hH : 2 * q + 2 ≤ H)
    (s : Finset ι) (A B : ι → ℝ) (n : ι → ℕ) (A0 : ℝ)
    (hA0 : 0 < A0) (hA : ∀ i ∈ s, 0 ≤ A i) (hB : ∀ i ∈ s, 0 ≤ B i) :
    ∀ᶠ w in l, ∀ (t m : ℕ) (theta : ℝ[X]) (p : ℕ → ℕ)
      (c k : ℕ → ι → ℤ) (u : ℕ → ι → ℝ), 0 < m →
      (∀ r, r.Prime → r ∣ m → r ≤ W w) →
      (∀ z : ℕ, z < H → S w ≤ (t + m * z : ℕ) ∧ (t + m * z : ℕ) < 2 * S w) →
      (∀ z : ℕ, z < H → (primorial (W w)).Coprime (t + m * z)) →
      ((C (t : ℝ) + C (m : ℝ) * X) ^ e * theta).natDegree ≤ q →
      (∀ z, z < H → p z = 1 ∨ p z = t + m * z) →
      (∀ z, z < H → ∀ i ∈ s, |(c z i : ℝ)| ≤ B i * (p z : ℝ) ^ n i) →
      (∀ z, z < H → ∀ i ∈ s,
        |u z i - (k z i : ℝ)| ≤ A i * (Z w)⁻¹ ^ (e + n i)) →
      (∀ z, z < H →
        ‖(((p z : ℝ) ^ e * (theta.eval (z : ℝ) + ∑ i ∈ s, (c z i : ℝ) * u z i) : ℝ) : UnitAddCircle)‖ ≤
          A0 * ((p z : ℝ) / Z w) ^ e) →
      ∃ M : ℚ[X], M.natDegree ≤ q - e ∧
        (∀ j r, r.Prime → r ∣ (M.coeff j).den → r ≤ W w) ∧
        ∀ z : ℕ, z < H → (∃ b : ℤ, M.eval (z : ℚ) = b) ∧
          |theta.eval (z : ℝ) - ((M.eval (z : ℚ) : ℚ) : ℝ)| ≤
            roughInterpolationConstant q * (2 ^ e * (A0 + ∑ i ∈ s, B i * A i)) * (Z w)⁻¹ ^ e := by
  let K := A0 + ∑ i ∈ s, B i * A i
  have hsum : 0 ≤ ∑ i ∈ s, B i * A i := Finset.sum_nonneg fun i hi => mul_nonneg (hB i hi) (hA i hi)
  have hK : 0 < K := by dsimp [K]; linarith
  have hlarge := hg.eventually_bound (hZ.mono fun _ h => h.le)
    (hS.mono fun _ h => by linarith) 1 (A := 2) (by norm_num)
  have hinterp := rough_exact_interpolation_mod_one hW hg hS hZ e q H he heq hH
    (2 ^ e * K) (by positivity)
  filter_upwards [hinterp, hlarge, hS, hZ] with w hw hlarge hs hz
  intro t m theta p c k u hm hmsmooth hprog hrough hdeg hp hc hu hobs
  apply hw t m theta hm hmsmooth hprog hrough hdeg
  intro z hzH
  have ht := (hprog z hzH).2.le
  have hps : (p z : ℝ) ≤ 2 * S w := by
    rcases hp z hzH with hp | hp
    · rw [hp, Nat.cast_one]; linarith
    · rw [hp]; exact ht
  have hpZ : (p z : ℝ) ≤ Z w := hps.trans (by simpa only [pow_one] using hlarge)
  have hd := rough_mod_one_descending_coefficient s (p z) e (theta.eval (z : ℝ)) (Z w)
    A0 (c z) (k z) (u z) A B n hz hpZ hA hB (hc z hzH) (hu z hzH) (hobs z hzH)
  apply rough_mod_one_sample_step_transfer ht hz hK.le e _ hd
  rcases hp z hzH with hp | hp
  · exact Or.inl (by exact_mod_cast hp)
  · exact Or.inr (by exact_mod_cast hp)

end Hindman168
