/-
Copyright OpenAI contributors. Licensed under Apache-2.0; see dependencies/openai-finite-szemeredi/LICENSE.
Original source: openai/math commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Modified for Lean 4.32.2 / mathlib 905b958 compatibility.
Original hashes and exact compatibility changes:
dependencies/openai-finite-szemeredi/NATIVE-INVERSE-SOURCE-MANIFEST.json.
-/
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

namespace OAI

section

namespace Erdos3

open scoped Manifold

def tangentModelVector {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {x : M} (v : TangentSpace I x) : E := v

end Erdos3

end

end OAI
