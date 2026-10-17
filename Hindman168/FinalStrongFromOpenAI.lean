import Hindman168.OriginalNativeIntervalInverse
import Hindman168.FinalStrongFromNativeInverse

/-!
Final library assembly for Lake DAG verification.

This module combines the fixed OpenAI inverse endpoint with the local
same-step native-model adapter. Verification status is recorded in
`verification/original-final-target`; the full chain must be built and
audited before any completion claim. It is not imported by the old
canonical aggregate. Do not import the preserved work-in-progress assembly
alongside this module, since both declare `strongConjecture_from_openai`.
-/

namespace Hindman168

/-- Final assembly from the fixed OpenAI inverse endpoint and the local
same-step native-model adapter. -/
theorem strongConjecture_from_openai : StrongConjecture :=
  strongConjecture_of_native_inverse.{0}
    native_periodic_interval_inverse_family_from_openai

end Hindman168
