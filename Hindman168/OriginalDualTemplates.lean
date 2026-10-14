import Hindman168.MasterSingleOriginalDenseModel

/-!
# Finite collections of original local dual templates

Each template keeps its own dimension, prime arity, polynomial tests,
designated denominator, gap and finite quotient-scale choice. All templates
embed in the same fixed original master list.
-/

namespace Hindman168

open Filter
open scoped Topology Classical

structure OriginalDualTemplate (n N K : ℕ) where
  dimension : ℕ
  arity : ℕ
  gap : ℕ → Fin N
  choice : ℕ → Fin K
  tests : Finset (MvPolynomial (Fin arity) ℤ)
  denominator : MvPolynomial (Fin arity) ℤ
  denominator_mem : denominator ∈ tests
  masterSlot : Fin arity → Fin n
  masterSlot_injective : Function.Injective masterSlot

structure OriginalDualTemplateConditions {n N K : ℕ} (T : OriginalDualTemplate n N K)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (d : ℕ)
    (tail : ℕ → Finset ℕ) (root : ℕ → Fin N) : Prop where
  dimension_pos : 0 < T.dimension
  dimension_le : T.dimension ≤ d
  polynomial_inclusion : ∀ f ∈ T.tests, MvPolynomial.rename T.masterSlot f ∈ D
  tail_gap : ∀ᶠ w in atTop, tail w ⊆ Finset.range (T.gap w).val
  gap_root : ∀ᶠ w in atTop, (T.gap w).val ≤ (root w).val

noncomputable def OriginalDualTemplate.dual {n N K : ℕ}
    (T : OriginalDualTemplate n N K) (F : MasterParameterFamily) (J : Fin K → ℕ)
    (u : OriginalSingleDualInput T.arity T.dimension) (w : ℕ) (y : ℤ) : ℝ :=
  masterSingleGoodDualTest F T.dimension T.gap J T.choice T.tests T.denominator
    (fun _ => u.epsilon) (fun _ => u.vertexTest) w y

noncomputable def signedOriginalClippedUnion {n N K m L : ℕ}
    (T : Fin L → OriginalDualTemplate n N K)
    (F : MasterParameterFamily) (C : ℕ → Chain m) (label : ℕ → Fin m)
    (J : Fin K → ℕ) (cut : ℝ) (w : ℕ) : Set (ℤ → ℝ) :=
  ⋃ t, signedOriginalSingleClippedClass (a := (T t).arity) (d := (T t).dimension)
    F C label (T t).gap J (T t).choice (T t).tests (T t).denominator cut w

theorem signedOriginalClippedUnion_abs_le {n N K m L : ℕ}
    (T : Fin L → OriginalDualTemplate n N K)
    (F : MasterParameterFamily) (C : ℕ → Chain m) (label : ℕ → Fin m)
    (J : Fin K → ℕ) (cut : ℝ) (hcut : 0 ≤ cut) (w : ℕ) {f : ℤ → ℝ}
    (hf : f ∈ signedOriginalClippedUnion T F C label J cut w) : ∀ y, |f y| ≤ cut := by
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hf
  exact signedOriginalSingleClippedClass_abs_le F C label (T t).gap J (T t).choice
    (T t).tests (T t).denominator cut hcut w ht

theorem signedOriginalClippedUnion_neg {n N K m L : ℕ}
    (T : Fin L → OriginalDualTemplate n N K)
    (F : MasterParameterFamily) (C : ℕ → Chain m) (label : ℕ → Fin m)
    (J : Fin K → ℕ) (cut : ℝ) (w : ℕ) {f : ℤ → ℝ}
    (hf : f ∈ signedOriginalClippedUnion T F C label J cut w) :
    -f ∈ signedOriginalClippedUnion T F C label J cut w := by
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hf
  exact Set.mem_iUnion.mpr ⟨t, signedOriginalSingleClippedClass_neg F C label
    (T t).gap J (T t).choice (T t).tests (T t).denominator cut w ht⟩

theorem signedOriginalClippedUnion_nonempty {n N K m L : ℕ}
    (T : Fin L → OriginalDualTemplate n N K) (hL : 0 < L)
    (F : MasterParameterFamily) (C : ℕ → Chain m) (label : ℕ → Fin m)
    (J : Fin K → ℕ) (cut : ℝ) (w : ℕ)
    (hν : ∀ y, 0 ≤ masterPredictionBlockMask F C label w y) :
    (signedOriginalClippedUnion T F C label J cut w).Nonempty := by
  let t : Fin L := ⟨0, hL⟩
  obtain ⟨f, hf⟩ := signedOriginalSingleClippedClass_nonempty (a := (T t).arity)
    (d := (T t).dimension) F C label (T t).gap J (T t).choice (T t).tests
    (T t).denominator cut w hν
  exact ⟨f, Set.mem_iUnion.mpr ⟨t, hf⟩⟩

end Hindman168
