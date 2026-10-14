# JSP-000168 — ongoing Lean formalization

Private working repository for continuing the formalization while travelling.
JSP-000168 corresponds to **Erdős problem #172**, not Erdős #168.

**The full target `Hindman168.StrongConjecture` is not proved.**
The repository contains substantial checked partial results following the
OpenAI paper, together with author-side build, source and axiom audits.
These checks are not an independent kernel replay or external peer review.
No prize application has been submitted. Keep this repository private until
the owner decides to publish it for the eventual application.

## Resume on another machine

Install Git, Python 3, and Lean's `elan` toolchain manager, then:

```sh
git clone https://github.com/lixiang90/jsp168-hindman.git
cd jsp168-hindman
python scripts/verify_snapshot.py
lake exe cache get
lake build
lake env lean Verification.lean
```

The clone requires access to this private repository. `lean-toolchain` pins
Lean 4.32.2. `lakefile.toml` pins mathlib to
`905b95818eb32af7874a58b427f50c1711a5e96c`.
Lake fetches dependencies from the committed lockfile. Avoid `lake update`
during routine setup; review any proposed change to `lake-manifest.json`
before committing it. Do not upgrade Lean or mathlib as part of setup.
The included PNTPlus and attributed OpenAI finite-Szemerédi source modules
are already in this repository. `.lake` build caches are not uploaded.

To run the build and axiom check together and save fresh local evidence:

```sh
python scripts/verify_snapshot.py --build
```

This first checks the exact source hashes in `verification-manifest.json`,
then builds and checks the registered declarations' axiom dependencies.
Fresh logs go in the ignored `verification-local/` directory. A successful
run verifies this checkpoint; it does not prove the unfinished main theorem.

## Current checkpoint and next step

- `CURRENT-STATUS.txt`: authoritative latest terminal audit and remaining work.
- `verification-manifest.json`: audited files, SHA-256 hashes and pinned sources.
- `STANDARD-FACE-HAAR-CONTINUATION.txt`: detailed latest interfaces and next proof step.
- `SELECTED-CUBE-PROJECTION-CONTINUATION.txt`: preceding exact array/cube projection.
- `EMPIRICAL-CUBE-INVARIANCE-CONTINUATION.txt`: preceding analytic invariance transfer.
- `COMMON-POINT-CUBE-CONTINUATION.txt`: preceding common-witness point/cube checkpoint.
- `CUBE-ALPHA-LIMIT-CONTINUATION.txt`: preceding explicit ordered-limit checkpoint.
- `ORIGINAL-CUBE-LOCAL-CONTINUATION.txt`: preceding original cube radius law.
- `CUBE-BOX-HAAR-CONTINUATION.txt`: preceding internal cube Haar checkpoint.
- `CUBE-SOURCE-CONTINUATION.txt`: preceding actual cube source checkpoint.
- `CUBE-BINOMIAL-CONTINUATION.txt`: preceding coefficient construction checkpoint.
- `CUBE-CHARACTER-CONTINUATION.txt`: preceding character construction checkpoint.
- `AUDIT.txt` and `round-*-review.json`: accumulated mathematical reviews.
- `Hindman168.lean`: canonical project imports.
- `Verification.lean`: registered axiom checks.

The latest mathematical round is `round-native-standard-face-haar`; consult
`CURRENT-STATUS.txt` and the manifest for its terminal audit result. One original
factorization and one chosen smooth curve now give BOTH point and cube local
laws, bounded alpha-box laws, continuous point-Haar integrals, and the actual
global point-mixture weak limit on the SAME subsequence and data. Projected
cube Haar full support and its measure-to-setwise-symmetry implication are proved.

For a fixed target component family, actual positive-event selection now yields
projected face Haar invariance on one common original-source subsequence,
filtration, period and smooth curve. Standard windows and the genuine real
source are connected exactly; good-condition and local-Haar premises are
discharged by their actual constructions in the final selected theorem.

The next task assembles all target marginals of ONE full heterogeneous joint
family, preserving common witnesses, then applies the support bridge and proves
joint lifts. Full Alignment, the remaining GTZ inverse work and the final
same-color FS/FP argument are still outstanding.

Continue from the same original source, final subgroup filtration and
original nilpotency bound. Do not replace the target with a weaker result,
assume a source/Haar/character/inverse oracle, introduce `sorry` or new
axioms, or claim the anticipated scalar is a polynomial coefficient before
proving that identity.

## Audit records and provenance

The current author-side evidence remains in `BUILD-EVIDENCE.txt`,
`round-native-standard-face-haar-axioms.txt`, and the latest round's review
and result records. The immediately preceding
`round-native-selected-cube-projection-axioms.txt` is retained because the
current round audit compares against it.

467 superseded `round-*-axioms.txt` output logs (300,418,280 bytes) have been
removed from the working tree. They contain repeated registered axiom reports,
not proof source or mathematical reviews. All mathematical reviews, source
provenance, dependency certificates, and verification-manifest entries remain.

Historical round scripts and review records describe their original checkpoints;
their old log paths and hashes refer to the
[pre-cleanup snapshot](https://github.com/lixiang90/jsp168-hindman/tree/e5e45b1e1227a8df34ee95eadd4b8d87b4811c74).
To inspect or recover an old report, open that snapshot or use
`git show e5e45b1e1227a8df34ee95eadd4b8d87b4811c74:REPORT-PATH`.
For historical audit replay, use a separate worktree with the matching source
checkpoint and its original logs. Old scripts may require removed predecessor
reports; do not run them against the current working tree as a current audit.
Some also require original Windows paths and local pinned paper/PNTPlus checkouts.

Use `scripts/verify_snapshot.py` for the portable current checkpoint check.
Its rules and all audited sources are unchanged by this documentation cleanup.

`work-in-progress/` and root-level scratch files are retained for continuity;
they are not automatically part of the canonical build or a claim of proof.

The paper source is pinned to OpenAI/math commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Dependency attribution and licenses are preserved in `PNTPLUS-ATTRIBUTION.txt`,
`LICENSE-PNTPLUS`, and `dependencies/openai-finite-szemeredi/`.
No new blanket license is assigned to the project's original contributions
by this checkpoint upload.
