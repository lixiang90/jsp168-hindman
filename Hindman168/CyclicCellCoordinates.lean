import Hindman168.MasterInteriorRenormalization
import Mathlib.Data.ZMod.Basic

namespace Hindman168

theorem completeResidueCell_cyclic_mean (k : ℤ) (M q : ℕ) [NeZero q]
    (r : Fin M) (f : ℤ → ℝ) :
    finiteHaarMean (fun t : Fin q => f (completeResidueCellPoint k M q r t)) =
      finiteHaarMean (fun z : ZMod q => f (k * (M * q : ℕ) + r.val + (M : ℤ) * z.val)) := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => rfl

theorem zmod_add_val_of_no_wrap (q : ℕ) [NeZero q] (z : ZMod q) (h : ℤ)
    (hl : 0 ≤ (z.val : ℤ) + h) (hu : (z.val : ℤ) + h < q) :
    ((z + (h : ZMod q)).val : ℤ) = z.val + h := by
  have he : (((z.val : ℤ) + h : ℤ) : ZMod q) = z + (h : ZMod q) := by
    simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [← he, ZMod.val_intCast, Int.emod_eq_of_lt hl hu]

theorem completeResidueCell_cyclic_shift (k : ℤ) (M q : ℕ) [NeZero q]
    (hM : 0 < M) (r : Fin M) (z : ZMod q) (h : ℤ)
    (hl : k * (M * q : ℕ) ≤ k * (M * q : ℕ) + r.val + (M : ℤ) * z.val + M * h)
    (hu : k * (M * q : ℕ) + r.val + (M : ℤ) * z.val + M * h <
      k * (M * q : ℕ) + (M * q : ℕ)) :
    k * (M * q : ℕ) + r.val + (M : ℤ) * (z + (h : ZMod q)).val =
      k * (M * q : ℕ) + r.val + (M : ℤ) * z.val + M * h := by
  have hm : (0 : ℤ) < M := by exact_mod_cast hM
  have hr : (r.val : ℤ) < M := by exact_mod_cast r.isLt
  have hr0 := Int.natCast_nonneg r.val
  have hlo : 0 ≤ (z.val : ℤ) + h := by
    by_contra hn
    have hh : (z.val : ℤ) + h ≤ -1 := by omega
    nlinarith
  have hhi : (z.val : ℤ) + h < q := by
    push_cast at hu
    by_contra hn
    have hh : (q : ℤ) ≤ z.val + h := by omega
    nlinarith
  rw [zmod_add_val_of_no_wrap q z h hlo hhi]
  ring

open scoped BigOperators

theorem completeResidueCell_integerMass_cyclic_error (X W : ℕ) (k : ℤ) (M q : ℕ) [NeZero q]
    (hM : 0 < M) (hWM : W ∣ M) (r : Fin M) (hr : r.val.Coprime W)
    (hZ : 0 < harmonicNormalizer X W)
    (hlo : (X : ℤ) ≤ k * (M * q : ℕ))
    (hhi : k * (M * q : ℕ) + (M * q : ℕ) ≤ (X ^ 2 : ℕ))
    (hA : 0 < (k : ℝ) * (M * q : ℕ)) (f : ℤ → ℝ) (hf : ∀ y, |f y| ≤ 1) :
    |(∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val, integerMass X W y * f y) /
      (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val, integerMass X W y) -
      finiteHaarMean (fun z : ZMod q => f (k * (M * q : ℕ) + r.val + (M : ℤ) * z.val))| ≤
      (M * q : ℕ) / ((k : ℝ) * (M * q : ℕ)) := by
  rw [← completeResidueCell_cyclic_mean k M q r f]
  exact completeResidueCell_integerMass_error X W k M q hM (Nat.pos_of_ne_zero (NeZero.ne q))
    hWM r hr hZ hlo hhi hA f hf

end Hindman168
