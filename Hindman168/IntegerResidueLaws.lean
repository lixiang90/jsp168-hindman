import Hindman168.UniformIntervals
import Hindman168.FinitePushContraction
import Hindman168.UniformCRT

/-!
# Actual integer interval and harmonic laws on ZMod

The finite representative laws are transported through an explicit
equivalence with ZMod. The interval and harmonic L1 bounds therefore
apply at exactly the integer congruence modulus used by the row kernel.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem uniformFintypeMass_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) :
    (uniformFintypeMass α).mapDomain e = uniformFintypeMass β := by
  ext b
  rw [Finsupp.mapDomain_equiv_apply, uniformFintypeMass_apply,
    uniformFintypeMass_apply, Fintype.card_congr e]

end Hindman168.FiniteMass

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

def finResidueEquiv (k : ℕ) [NeZero k] : Fin k ≃ ZMod k where
  toFun a := (a.val : ZMod k)
  invFun a := ⟨a.val, a.val_lt⟩
  left_inv a := Fin.ext (ZMod.val_natCast_of_lt a.isLt)
  right_inv a := ZMod.natCast_zmod_val a

theorem uniformResidueMass_zmod (k : ℕ) [NeZero k] :
    (uniformResidueMass k).mapDomain (finResidueEquiv k) = uniformFintypeMass (ZMod k) :=
  uniformFintypeMass_equiv (finResidueEquiv k)

theorem integerResidue_zmod (k : ℕ) (hk : 0 < k) [NeZero k] (z : ℤ) :
    finResidueEquiv k (integerResidue k hk z) = (z : ZMod k) := by
  have he := (integerResidue_eq_iff k hk z (integerResidue k hk z)).mp rfl
  change ((integerResidue k hk z).val : ZMod k) = _
  rw [← Int.cast_natCast, ← he, ZMod.intCast_mod]

theorem uniform_interval_zmod_distance (A : ℤ) {T k : ℕ} [NeZero k] (hT : 0 < T) :
    distance ((uniformIntervalMass A T).mapDomain (fun z : ℤ => (z : ZMod k)))
      (uniformFintypeMass (ZMod k)) ≤ (k : ℝ) / T := by
  have hk := Nat.pos_of_ne_zero (NeZero.ne k)
  have hm : ((intervalResidueMass A T k hk).mapDomain (finResidueEquiv k)) =
      (uniformIntervalMass A T).mapDomain (fun z : ℤ => (z : ZMod k)) := by
    rw [intervalResidueMass, ← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr (fun z _ => integerResidue_zmod k hk z)
  rw [← hm, ← uniformResidueMass_zmod k, distance_push_injective (finResidueEquiv k).injective]
  exact uniform_interval_residue_distance A hT hk

noncomputable def rawResidueMass (X W k : ℕ) (hk : 0 < k) : Mass (Fin k) :=
  (rawMass X W).mapDomain (fun n => ⟨n % k, Nat.mod_lt n hk⟩)

theorem rawResidueMass_apply (X W k : ℕ) (hk : 0 < k) (a : Fin k) :
    rawResidueMass X W k hk a = residueProbability X W k a.val := by
  have hs : (rawMass X W).support ⊆ harmonicWindow X W :=
    (intervalMass_support X (X ^ 2 : ℕ) W _).trans (unitInterval_raw X W).subset
  rw [rawResidueMass, push_apply, Finset.sum_subset hs (by
    intro n _ hn
    rw [Finsupp.notMem_support_iff.mp hn]
    split_ifs <;> rfl)]
  have he (n : ℕ) : a = (⟨n % k, Nat.mod_lt n hk⟩ : Fin k) ↔ n % k = a.val := by
    rw [Fin.ext_iff]
    exact eq_comm
  simp only [he, rawMass_apply]
  rw [← Finset.sum_filter]
  rfl

theorem harmonic_integer_zmod_distance {X W k : ℕ} [NeZero k]
    (hX : 2 ≤ X) (hW : 0 < W) (hco : W.Coprime k)
    (hlog : (W : ℝ) / X < Real.log (X : ℝ)) :
    distance ((integerMass X W).mapDomain (fun z : ℤ => (z : ZMod k)))
      (uniformFintypeMass (ZMod k)) ≤ residueError X W k := by
  have hk := Nat.pos_of_ne_zero (NeZero.ne k)
  have hm : (rawResidueMass X W k hk).mapDomain (finResidueEquiv k) =
      (integerMass X W).mapDomain (fun z : ℤ => (z : ZMod k)) := by
    rw [rawResidueMass, integerMass, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    apply Finsupp.mapDomain_congr
    intro n hn
    change ((n % k : ℕ) : ZMod k) = ((n : ℤ) : ZMod k)
    simp only [ZMod.natCast_mod, Int.cast_natCast]
  rw [← hm, ← uniformResidueMass_zmod k, distance_push_injective (finResidueEquiv k).injective,
    distance, variation_eq_sum _ (Finset.subset_univ _)]
  simp only [Finsupp.sub_apply, rawResidueMass_apply, uniformResidueMass_apply]
  exact harmonic_residue_total_mass_error hX hW hk hco hlog

end Hindman168
