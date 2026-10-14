import Hindman168.AlignmentFreeNilpotent

/-! Ordered monomial words and their exact interpretation under group
homomorphisms. No interchange of noncommuting letters is used. -/

namespace Hindman168

def alignmentMonomialWord {E G : Type*} [Group G]
    (L : E → G) (degree : E → ℕ) : List E → ℕ → G
  | [], _ => 1
  | e :: w, k => L e ^ (k ^ degree e) * alignmentMonomialWord L degree w k

theorem alignmentMonomialWord_append {E G : Type*} [Group G]
    (L : E → G) (degree : E → ℕ) (v w : List E) (k : ℕ) :
    alignmentMonomialWord L degree (v ++ w) k =
      alignmentMonomialWord L degree v k * alignmentMonomialWord L degree w k := by
  induction v with
  | nil => simp only [List.nil_append, alignmentMonomialWord, one_mul]
  | cons e v ih =>
    simp only [List.cons_append, alignmentMonomialWord, ih, mul_assoc]

theorem alignmentMonomialWord_map {E G H : Type*} [Group G] [Group H]
    (f : G →* H) (L : E → G) (degree : E → ℕ) (w : List E) (k : ℕ) :
    f (alignmentMonomialWord L degree w k) =
      alignmentMonomialWord (fun e => f (L e)) degree w k := by
  induction w with
  | nil => exact f.map_one
  | cons e w ih => simp only [alignmentMonomialWord, map_mul, map_pow, ih]

theorem alignmentMonomialWord_zero {E G : Type*} [Group G]
    (L : E → G) (degree : E → ℕ) (w : List E)
    (hdegree : ∀ e ∈ w, 0 < degree e) :
    alignmentMonomialWord L degree w 0 = 1 := by
  induction w with
  | nil => rfl
  | cons e w ih =>
    have he : degree e ≠ 0 := ne_of_gt (hdegree e (List.mem_cons_self))
    have hw : ∀ a ∈ w, 0 < degree a := fun a ha => hdegree a (List.mem_cons_of_mem e ha)
    simp only [alignmentMonomialWord, zero_pow he, pow_zero, one_mul, ih hw]

theorem alignmentMonomialWord_interpretation {E G : Type*} [Group G]
    (s : ℕ) (L : E → G) (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (degree : E → ℕ) (w : List E) (k : ℕ) :
    alignmentFreeInterpretation s L hG
      (alignmentMonomialWord (alignmentFreeGenerator s) degree w k) =
      alignmentMonomialWord L degree w k := by
  rw [alignmentMonomialWord_map]
  congr 1
  funext e
  exact alignmentFreeInterpretation_generator s L hG e

end Hindman168
