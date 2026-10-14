import Hindman168.PredictionStageProducts
import Hindman168.MaskGeneratedIntegerRowDirections

/-!
General integer rows for additive elimination. Existing canonical copy
indices are reused with a single nonempty vertex type; their evaluation
uses the actual row coefficients and directions, not replica-cube forms.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def additiveRowAssigned (b : ℕ) (i : Fin b) : Fin b × CubeVertex 1 :=
  (i, ⟨{0}, Finset.singleton_nonempty 0⟩)

theorem additiveRowAssigned_injective (b : ℕ) : Function.Injective (additiveRowAssigned b) := by
  intro i j h
  exact congrArg Prod.fst h

theorem additiveRowAssigned_surjective (b : ℕ) : Function.Surjective (additiveRowAssigned b) := by
  intro p
  refine ⟨p.1, ?_⟩
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    have hz : (0 : Fin 1) ∈ p.2.val := by
      obtain ⟨k, hk⟩ := p.2.property
      simpa only [Subsingleton.elim k (0 : Fin 1)] using hk
    ext j
    simp only [additiveRowAssigned, Finset.mem_singleton,
      Subsingleton.elim j (0 : Fin 1), hz]

structure AdditiveRowData (b c : ℕ) where
  coefficient : ReplicaCubeRow b 1 → Fin c → ℤ
  direction : Fin b → Fin c → ℤ
  annihilate : ∀ i, (∑ j, coefficient (some (additiveRowAssigned b i)) j * direction i j) = 0

namespace AdditiveRowData

variable {b c : ℕ}

noncomputable def form (D : AdditiveRowData b c) (i : ReplicaCubeRow b 1) (z : Fin c → ℤ) : ℤ :=
  ∑ j, D.coefficient i j * z j

noncomputable def response (D : AdditiveRowData b c) (i : ReplicaCubeRow b 1) (k : Fin b) : ℤ :=
  D.form i (D.direction k)

theorem response_own (D : AdditiveRowData b c) (k : Fin b) :
    D.response (some (additiveRowAssigned b k)) k = 0 := D.annihilate k

theorem form_add (D : AdditiveRowData b c) (i : ReplicaCubeRow b 1) (z v : Fin c → ℤ) :
    D.form i (fun j => z j + v j) = D.form i z + D.form i v := by
  simp only [form, mul_add, Finset.sum_add_distrib]

theorem form_sum (D : AdditiveRowData b c) (i : ReplicaCubeRow b 1)
    {ι : Type*} [Fintype ι] (z : ι → Fin c → ℤ) :
    D.form i (fun j => ∑ k, z k j) = ∑ k, D.form i (z k) := by
  simp only [form, Finset.mul_sum]
  exact Finset.sum_comm

theorem form_mul (D : AdditiveRowData b c) (i : ReplicaCubeRow b 1) (z : Fin c → ℤ) (t : ℤ) :
    D.form i (fun j => t * z j) = t * D.form i z := by
  simp only [form, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

noncomputable def translatedForm (D : AdditiveRowData b c) (i : ReplicaCubeRow b 1)
    (η : Fin b → Bool) (z : Fin c → ℤ) (v : Fin b → Bool → ℤ) : ℤ :=
  D.form i z + ∑ k, D.response i k * v k (η k)

theorem translatedForm_eq_translate (D : AdditiveRowData b c) (i : ReplicaCubeRow b 1)
    (η : Fin b → Bool) (z : Fin c → ℤ) (v : Fin b → Bool → ℤ) :
    D.translatedForm i η z v = D.form i (fun j => z j + ∑ k, v k (η k) * D.direction k j) := by
  rw [D.form_add, D.form_sum]
  simp only [D.form_mul, translatedForm, response]
  congr 1
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

end AdditiveRowData
end Hindman168
