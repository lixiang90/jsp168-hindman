import Hindman168.RamseyEnergySelection

/-! The last two entries of the paper's increasing tuple are the gap
and pivot. Deleting them recovers the same tail in both compared tuples. -/

namespace Hindman168

def energyTuple (T : Finset ℕ) (l i : ℕ) : Finset ℕ := insert i (insert l T)

def energyTuplePivot (A : Finset ℕ) : ℕ := A.sup id

def energyTupleGap (A : Finset ℕ) : ℕ := (A.erase (energyTuplePivot A)).sup id

def energyTupleTail (A : Finset ℕ) : Finset ℕ :=
  (A.erase (energyTuplePivot A)).erase (energyTupleGap A)

theorem energyTuple_decode (T : Finset ℕ) (l i : ℕ)
    (hT : ∀ t ∈ T, t < l) (hli : l < i) :
    energyTuplePivot (energyTuple T l i) = i ∧
    energyTupleGap (energyTuple T l i) = l ∧
    energyTupleTail (energyTuple T l i) = T := by
  have hl : l ∉ T := fun h => (lt_irrefl l) (hT l h)
  have hi : i ∉ T := fun h => (not_lt_of_ge hli.le) (hT i h)
  have his : i ∉ insert l T := by simp [hi, ne_of_gt hli]
  have hs : T.sup id ≤ l := Finset.sup_le (fun t ht => (hT t ht).le)
  have hp : energyTuplePivot (energyTuple T l i) = i := by
    simp only [energyTuplePivot, energyTuple, Finset.sup_insert, id_eq]
    exact max_eq_left (max_le hli.le (hs.trans hli.le))
  have hg : energyTupleGap (energyTuple T l i) = l := by
    rw [energyTupleGap, hp]
    simp only [energyTuple, Finset.erase_insert his,
      Finset.sup_insert, id_eq]
    exact max_eq_left hs
  refine ⟨hp, hg, ?_⟩
  rw [energyTupleTail, hp, hg]
  simp only [energyTuple, Finset.erase_insert his,
    Finset.erase_insert hl]

theorem energyTuple_card (T : Finset ℕ) (l i : ℕ)
    (hT : ∀ t ∈ T, t < l) (hli : l < i) : (energyTuple T l i).card = T.card + 2 := by
  have hl : l ∉ T := fun h => (lt_irrefl l) (hT l h)
  have hi : i ∉ T := fun h => (not_lt_of_ge hli.le) (hT i h)
  simp [energyTuple, hl, hi, ne_of_gt hli, Nat.add_assoc]

theorem energyTuple_subset {T S : Finset ℕ} {l i : ℕ}
    (hT : T ⊆ S) (hl : l ∈ S) (hi : i ∈ S) : energyTuple T l i ⊆ S :=
  Finset.insert_subset hi (Finset.insert_subset hl hT)

end Hindman168

