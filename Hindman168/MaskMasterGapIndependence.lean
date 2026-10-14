import Hindman168.MaskGeneratedOriginalTemplates

/-! The actual mask-generated master catalogue uses row coefficients and
slots, which are independent of the later gap metadata. This removes a
potential circularity when selecting principal and padding indices. -/

namespace Hindman168
open scoped Classical

theorem maskGeneratedMasterCatalog_gap_independent (m : ℕ) {N K : ℕ}
    (gap : ℕ → Fin N) (other : ℕ → Fin K) :
    originalRowMasterCatalog (maskGeneratedRowDataFamily m gap) =
      originalRowMasterCatalog (maskGeneratedRowDataFamily m other) := by
  rfl

theorem maskGeneratedMaster_gap_independent (m : ℕ) {N : ℕ}
    (gap other : ℕ → Fin N) :
    maskGeneratedMaster m gap = maskGeneratedMaster m other := by
  rfl

end Hindman168
