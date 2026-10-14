import Hindman168.FiniteVectorPolynomialSums
import Hindman168.FiniteVectorPolynomialIntegral

namespace Hindman168

def finiteVectorPolynomialDegreeLE {E : Type*} (p : List (ℕ × E)) (d : ℕ) : Prop :=
  ∀ a ∈ p, a.1 ≤ d

theorem finiteVectorPolynomialDegreeLE_mono {E : Type*} {p : List (ℕ × E)} {d e : ℕ}
    (hp : finiteVectorPolynomialDegreeLE p d) (hde : d ≤ e) : finiteVectorPolynomialDegreeLE p e :=
  fun a ha => (hp a ha).trans hde

theorem finiteVectorPolynomialDegreeLE_singleton {E : Type*} (a : E) (d : ℕ) :
    finiteVectorPolynomialDegreeLE [(d, a)] d := by
  intro b hb
  simpa only [List.mem_singleton.mp hb] using Nat.le_refl d

theorem finiteVectorPolynomialDegreeLE_append {E : Type*} {p q : List (ℕ × E)} {d : ℕ}
    (hp : finiteVectorPolynomialDegreeLE p d) (hq : finiteVectorPolynomialDegreeLE q d) :
    finiteVectorPolynomialDegreeLE (p ++ q) d := by
  intro a ha
  exact (List.mem_append.mp ha).elim (hp a) (hq a)

theorem finiteVectorPolynomialDegreeLE_sum {E : Type*} (n d : ℕ) (P : ℕ → List (ℕ × E))
    (hP : ∀ j < n, finiteVectorPolynomialDegreeLE (P j) d) :
    finiteVectorPolynomialDegreeLE (finiteVectorPolynomialSum n P) d := by
  intro a ha
  obtain ⟨p, hp, hap⟩ := List.mem_flatten.mp ha
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
  exact hP j (List.mem_range.mp hj) a hap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]

omit [NormedSpace ℝ E] in
theorem finiteVectorPolynomialDegreeLE_scale {p : List (ℕ × E)} {d : ℕ}
    (hp : finiteVectorPolynomialDegreeLE p d) (r : ℚ) :
    finiteVectorPolynomialDegreeLE (finiteVectorPolynomialScale r p) d := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact hp b hb

omit [NormedSpace ℝ E] in
theorem finiteVectorPolynomialDegreeLE_primitive {p : List (ℕ × E)} {d : ℕ}
    (hp : finiteVectorPolynomialDegreeLE p d) :
    finiteVectorPolynomialDegreeLE (finiteVectorPolynomialPrimitive p) (d + 1) := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact Nat.add_le_add_right (hp b hb) 1

omit [Module ℚ E] in
theorem finiteVectorPolynomialDegreeLE_bilinear
    (B : E →L[ℝ] (E →L[ℝ] E)) {p q : List (ℕ × E)} {d e : ℕ}
    (hp : finiteVectorPolynomialDegreeLE p d) (hq : finiteVectorPolynomialDegreeLE q e) :
    finiteVectorPolynomialDegreeLE (finiteVectorPolynomialBilinear B p q) (d + e) := by
  intro a ha
  obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  exact Nat.add_le_add (hp b hb) (hq c hc)

omit [Module ℚ E] in
theorem finiteVectorPolynomialDegreeLE_adPower
    (B : E →L[ℝ] (E →L[ℝ] E)) {p q : List (ℕ × E)} {d e : ℕ}
    (hp : finiteVectorPolynomialDegreeLE p d) (hq : finiteVectorPolynomialDegreeLE q e) (n : ℕ) :
    finiteVectorPolynomialDegreeLE (finiteVectorPolynomialAdPower B p q n) (n * d + e) := by
  induction n with
  | zero => simpa only [finiteVectorPolynomialAdPower, zero_mul, zero_add] using hq
  | succ n ih =>
    have h := finiteVectorPolynomialDegreeLE_bilinear B hp ih
    simpa only [finiteVectorPolynomialAdPower, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm] using h

end Hindman168
