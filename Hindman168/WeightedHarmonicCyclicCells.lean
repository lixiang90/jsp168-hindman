import Hindman168.IntegerShortCubeGowersBound

namespace Hindman168
open scoped BigOperators

theorem weighted_completeCell_harmonic_cyclic_error {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1)
    (X W M q : ℕ) [NeZero q] (hX : 0 < X) (hM : 0 < M) (hWM : W ∣ M)
    (hZ : 0 < harmonicNormalizer X W) (k : ι → ℤ) (r : ι → Fin M)
    (hr : ∀ c, (r c).val.Coprime W)
    (hlo : ∀ c, (X : ℤ) ≤ k c * (M * q : ℕ))
    (hhi : ∀ c, k c * (M * q : ℕ) + (M * q : ℕ) ≤ (X ^ 2 : ℕ))
    (f : ι → ℤ → ℝ) (hf : ∀ c y, |f c y| ≤ 1) :
    |(∑ c, p c * ((∑ y ∈ intervalResidueSet (k c * (M * q : ℕ)) (M * q) M (r c).val,
        integerMass X W y * f c y) /
      (∑ y ∈ intervalResidueSet (k c * (M * q : ℕ)) (M * q) M (r c).val, integerMass X W y))) -
      ∑ c, p c * finiteHaarMean (fun z : ZMod q =>
        f c (k c * (M * q : ℕ) + (r c).val + (M : ℤ) * z.val))| ≤ (M * q : ℕ) / (X : ℝ) := by
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  apply weightedCell_test_error p _ _ hp hs
  intro c
  have ha : (X : ℝ) ≤ (k c : ℝ) * (M * q : ℕ) := by exact_mod_cast hlo c
  exact (completeResidueCell_integerMass_cyclic_error X W (k c) M q hM hWM (r c) (hr c)
    hZ (hlo c) (hhi c) (hx.trans_le ha) (f c) (hf c)).trans
    (div_le_div_of_nonneg_left (Nat.cast_nonneg (M * q)) hx ha)

end Hindman168
