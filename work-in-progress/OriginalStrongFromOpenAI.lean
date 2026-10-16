import «work-in-progress».OriginalNativeIntervalAdapter
import Hindman168.FinalStrongFromNativeInverse

/-!
Uncompiled final assembly, outside the verified library and its manifest.

The quoted Lean module name above names the real `work-in-progress/` directory.
It requires the repository root on `LEAN_PATH` and a previously compiled
`work-in-progress/OriginalNativeIntervalAdapter.olean`. This file must not be
reported as verified until that import and the complete dependency closure
have been compiled with the pinned toolchain.
-/

namespace Hindman168

/-- Final assembly from the fixed OpenAI inverse endpoint and the local
same-step native-model adapter. Draft: not yet kernel-checked. -/
theorem strongConjecture_from_openai : StrongConjecture :=
  strongConjecture_of_native_inverse.{0}
    native_periodic_interval_inverse_family_from_openai

end Hindman168
