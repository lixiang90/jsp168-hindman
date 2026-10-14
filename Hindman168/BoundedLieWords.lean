import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Data.Set.Finite.List

/-! Actual right-nested Lie words in the original Lie algebra. Their
length places them in the actual lower central series. Bounded words over
an actual finite generating set form an actual finite set of vectors. -/

namespace Hindman168
open Function Set Submodule

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

def lieWordValue (xs : List L) (w : L) : L := xs.foldr (fun x y => ⁅x, y⁆) w

 theorem lieWordValue_nil (w : L) : lieWordValue [] w = w := rfl

 theorem lieWordValue_cons (x : L) (xs : List L) (w : L) :
    lieWordValue (x :: xs) w = ⁅x, lieWordValue xs w⁆ := rfl

 theorem lieWordValue_mem_lowerCentral (xs : List L) (w : L) :
    lieWordValue xs w ∈ LieModule.lowerCentralSeries R L L xs.length := by
  induction xs with
  | nil => rw [lieWordValue_nil, List.length_nil, LieModule.lowerCentralSeries_zero]; trivial
  | cons x xs ih =>
    rw [lieWordValue_cons, List.length_cons, LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) ih

 theorem lieWordValue_zero_of_lowerCentral_bot {c : ℕ}
    (hc : LieModule.lowerCentralSeries R L L c = ⊥) (xs : List L) (w : L)
    (hlen : c ≤ xs.length) : lieWordValue xs w = 0 := by
  have hmem := LieModule.antitone_lowerCentralSeries R L L hlen
    (lieWordValue_mem_lowerCentral (R := R) xs w)
  rw [hc] at hmem
  exact hmem

def boundedLieWordValues (s : Set L) (c : ℕ) : Set L :=
  range (fun p : {xs : List s // xs.length ≤ c} × s =>
    lieWordValue (p.1.val.map (fun x : s => x.val)) p.2.val)

 theorem boundedLieWordValues_finite (s : Set L) (hs : s.Finite) (c : ℕ) :
    (boundedLieWordValues s c).Finite := by
  letI : Fintype s := hs.fintype
  letI : Fintype {xs : List s // xs.length ≤ c} := (List.finite_length_le s c).fintype
  exact Set.finite_range _

 theorem subset_boundedLieWordValues (s : Set L) (c : ℕ) : s ⊆ boundedLieWordValues s c := by
  intro w hw
  exact ⟨(⟨[], by simp⟩, ⟨w, hw⟩), rfl⟩

 theorem lieWordValue_subtype_mem_lieSpan (s : Set L) (xs : List s) (w : s) :
    lieWordValue (xs.map (fun x : s => x.val)) w.val ∈ LieSubalgebra.lieSpan R L s := by
  induction xs with
  | nil => exact LieSubalgebra.subset_lieSpan w.property
  | cons x xs ih =>
    exact (LieSubalgebra.lieSpan R L s).lie_mem (LieSubalgebra.subset_lieSpan x.property) ih

end Hindman168
