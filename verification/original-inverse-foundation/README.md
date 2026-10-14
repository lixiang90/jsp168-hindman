# Original OpenAI BCH / native-model foundation

This batch integrates the first 288 original OpenAI dependency modules
through `OAI.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry`.
Of these, 23 were already present and are reused byte-for-byte; 265 are new.
The source is OpenAI `math` commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, under Apache-2.0.
Lean remains 4.32.2 and mathlib remains
`905b95818eb32af7874a58b427f50c1711a5e96c`.

The original BCH construction provides actual real Lie groups, cocompact
lattices, quotient metrics and topology agreement, and quantitative
Lipschitz bounds for actual quotient maps. This is a prerequisite of the
finite native model adapter, not the GTZ inverse theorem itself.

`dependencies/openai-finite-szemeredi/NATIVE-INVERSE-SOURCE-MANIFEST.json`
records original hashes, compatibility differences and integrated hashes.
The initial isolated-port notices were adjusted to refer to the repository's
actual license and manifest paths; proof bodies were not changed during
integration. Existing vendor sources, canonical statements and the
historical snapshot manifest are unchanged.

## Reproduction

From the repository root with the pinned toolchain:

```
lake build OAI.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry
lake env lean --trust=0 verification/original-inverse-foundation/CheckAllAxioms.lean
python scripts/verify_snapshot.py
```

The audit enumerates every originating environment declaration in these
288 modules, including generated declarations, and rejects any axiom other
than `propext`, `Classical.choice`, and `Quot.sound`. Source hashes, the actual
build log and audit log are recorded alongside this file. A separate textual
scan rejects proof placeholders and unsafe proof-checking shortcuts.
No independent replay of the pinned mathlib library is claimed.

The full axiom log is stored losslessly as `axioms.log.gz`. Use
`gzip -dc axioms.log.gz > axioms.log` and compare `audit-log-sha256.txt`.
