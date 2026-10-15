import Hindman168.OriginalInverseNormalizationMean
import Hindman168.OriginalInverseNormalizationNumerics
import Hindman168.OriginalSupportedCubeInterval

/-! The final change of coordinates needed by the upstream inverse:
the one-dimensional integer interval is identified with its `Unit → ℤ`
encoding. All norm and reflection statements refer to the actual interval. -/

namespace Hindman168
open scoped BigOperators Classical
open OAI.Erdos3

def originalInverseIntervalEval : (Unit → ℤ) ≃+ ℤ where
  toFun x := x ()
  invFun n := fun _ => n
  left_inv x := by funext u; cases u; rfl
  right_inv n := rfl
  map_add' x y := rfl

@[simp] theorem originalInverseIntervalEval_apply (x : Unit → ℤ) :
    originalInverseIntervalEval x = x () := rfl

theorem originalInverseInterval_image_eval (L : ℕ) :
    (originalInverseInterval L).image originalInverseIntervalEval =
      Finset.Ico (0 : ℤ) L := by
  ext n
  constructor
  · intro hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Ico.mpr ((originalInverseInterval_mem x).mp hx)
  · intro hn
    refine Finset.mem_image.mpr ⟨fun _ => n, ?_, rfl⟩
    exact (originalInverseInterval_mem _).mpr (Finset.mem_Ico.mp hn)

theorem originalInverseInterval_gowersNorm (q d L : ℕ) (v : ZMod q → ℝ) :
    finiteSupportGowersNorm d (originalInverseInterval L)
      (fun x => (v (x () : ZMod q) : ℂ)) =
      integerIntervalPeriodicGowersValue q d L v := by
  have h := finiteSupportGowersNorm_addEquiv originalInverseIntervalEval d
    (originalInverseInterval L) (fun z : ℤ => (v (z : ZMod q) : ℂ))
  rw [originalInverseInterval_image_eval,
    finiteSupportGowersNorm_integerInterval] at h
  exact h.symm

theorem originalInverseInterval_encoding_reflectsPairSums {L : ℕ} (hL : 0 < L) :
    ReflectsPairSums
      ((Int.castAddHom (ZMod (2 * L))).comp originalInverseIntervalEval.toAddMonoidHom)
      (originalInverseInterval L : Set (Unit → ℤ)) := by
  intro a ha b hb c hc d hd he
  have ha' := (originalInverseInterval_mem a).mp ha
  have hb' := (originalInverseInterval_mem b).mp hb
  have hc' := (originalInverseInterval_mem c).mp hc
  have hd' := (originalInverseInterval_mem d).mp hd
  have he' : ((a () + b () : ℤ) : ZMod (2 * L)) =
      ((c () + d () : ℤ) : ZMod (2 * L)) := by
    simpa using he
  have hs := originalInverseInterval_pair_sums hL (a ()) (b ()) (c ()) (d ())
    ha' hb' hc' hd' he'
  funext u
  cases u
  exact hs

theorem originalInverseInterval_encoding_representatives {L : ℕ}
    (x : Unit → ℤ) (hx : x ∈ originalInverseInterval L) :
    0 ≤ originalInverseIntervalEval x ∧
      originalInverseIntervalEval x < ((2 * L : ℕ) : ℤ) := by
  have h := (originalInverseInterval_mem x).mp hx
  change 0 ≤ x () ∧ x () < ((2 * L : ℕ) : ℤ)
  push_cast
  omega

theorem originalInverseInterval_encoding_density {L : ℕ} (hL : 0 < L) :
    Real.exp (-1 : ℝ) ≤ ((originalInverseInterval L).card : ℝ) / (2 * L : ℕ) := by
  rw [originalInverseInterval_card]
  exact originalInverse_doubled_length_density_lower hL

end Hindman168
