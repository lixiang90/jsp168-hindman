/- Modified excerpt of PrimeNumberTheoremAnd at 747e480362ef6a0a7341055a84372333d72fa62a.
Original authors and contributors retain attribution; Apache-2.0.
Changes: removed blueprint annotations and the unused unfinished
alternative decay block. Retained proofs are unchanged. -/

import Mathlib.Algebra.Notation.Support

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function
