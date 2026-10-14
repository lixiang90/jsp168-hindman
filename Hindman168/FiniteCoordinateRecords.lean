import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Finite.Prod

/-! Finite coordinate ranges give finitely many complete records. An
actual finite image has a finite set of representatives in its source. -/

namespace Hindman168
open Set

 theorem finite_image_of_finite_coordinate_images {α β ι : Type*} [Finite ι]
    (T : Set α) (f : α → ι → β)
    (h : ∀ i, ((fun x => f x i) '' T).Finite) : (f '' T).Finite := by
  let R : ι → Set β := fun i => (fun x => f x i) '' T
  letI (i : ι) : Finite (R i) := h i
  have hf : (range (fun r : (∀ i, R i) => fun i => (r i).val)).Finite := finite_range _
  apply hf.subset
  rintro v ⟨x, hx, rfl⟩
  exact ⟨fun i => ⟨f x i, ⟨x, hx, rfl⟩⟩, rfl⟩

 theorem exists_finite_image_representatives {α β : Type*} (T : Set α) (f : α → β)
    (h : (f '' T).Finite) : ∃ D ⊆ T, D.Finite ∧ f '' D = f '' T := by
  apply (exists_subset_image_finite_and (f := f) (s := T) (p := fun U => U = f '' T)).mp
  exact ⟨f '' T, subset_rfl, h, rfl⟩

end Hindman168
