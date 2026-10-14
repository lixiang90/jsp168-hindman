# Actual nilpotent polynomial recurrence

`UpstreamNilpotentRecurrence` contains the complete self-contained cube-polynomial/PET/coloring-recurrence proof from OpenAI's pinned original `WordPlan01.lean`, lines 90–1680. The source is Apache-2.0, with explicit source attribution and compatibility modifications. Provenance records the full original file hash, exact slice hash, installed hash, and six API-only diff hunks; no mathematical statements or hypotheses were deleted.

`AlignmentNilpotentRecurrence` proves the existing `HasAlignmentMonomialRecurrence s` for every `s`. It encodes each actual ordered monomial word as an integer-polynomial word, proves the polynomials vanish at zero, and preserves both word order and left multiplication. The stronger adapter gives `k > N` for any prescribed `N`; the required interface uses `N = 0`. Nilpotence of the actual free nilpotent group follows from its proved lower-central-series bound.

`alignment_canonical_finite_word_plan_proved` supplies the original canonical plan without a recurrence-input hypothesis. This closes the previously explicit recurrence obligation. It does not by itself supply the geometric actions, Haar limit, positive alignment mass, or final Hindman theorem.

All three modules passed targeted Lake builds and independent `lake env lean --trust=0` source re-elaboration. The complete list of 287 module declarations, including generated auxiliaries, was audited; only `propext`, `Classical.choice`, and `Quot.sound` occur. Exact source/slice hashes were independently verified. The canonical imports and original verification manifest remain unchanged.
