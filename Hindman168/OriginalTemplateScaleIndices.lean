import Hindman168.OriginalDualTemplates

/-!
# Exact finite reindexing of constant original quotient scales

A finite prefix may include arbitrarily many positive J values, while the
original master list and arity remain fixed. The dual law is unchanged when
its constant scale is represented by an index in the prefix's scale array.
-/

namespace Hindman168

open scoped Classical

def OriginalDualTemplate.withScaleIndex {n N K K' : ℕ}
    (T : OriginalDualTemplate n N K) (index : Fin K') : OriginalDualTemplate n N K' where
  dimension := T.dimension
  arity := T.arity
  gap := T.gap
  choice := fun _ => index
  tests := T.tests
  denominator := T.denominator
  denominator_mem := T.denominator_mem
  masterSlot := T.masterSlot
  masterSlot_injective := T.masterSlot_injective

theorem OriginalDualTemplate.dual_withScaleIndex {n N K K' : ℕ}
    (T : OriginalDualTemplate n N K) (index : Fin K') (F : MasterParameterFamily)
    (J : Fin K' → ℕ) (u : OriginalSingleDualInput T.arity T.dimension) (w : ℕ) (y : ℤ) :
    (T.withScaleIndex index).dual F J u w y = T.dual F (fun _ => J index) u w y := rfl

theorem OriginalDualTemplate.withScaleIndex_conditions {n N K K' d : ℕ}
    (T : OriginalDualTemplate n N K) (index : Fin K')
    (D : Finset (MvPolynomial (Fin n) ℤ)) (tail : ℕ → Finset ℕ) (root : ℕ → Fin N)
    (hT : OriginalDualTemplateConditions T D d tail root) :
    OriginalDualTemplateConditions (T.withScaleIndex index) D d tail root :=
  ⟨hT.dimension_pos, hT.dimension_le, hT.polynomial_inclusion, hT.tail_gap, hT.gap_root⟩

end Hindman168
