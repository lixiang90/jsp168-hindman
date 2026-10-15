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

## Current status

The original `StrongConjecture` remains unfinished. Uniform Alignment, the
finite native model family, and same-step linearization are proved. The full
upstream Axis inverse closure is being compiled and checked before final assembly.
See [the current verification overview](verification/README.md) for the single
current status index and exact validation boundaries.

`Hindman168.lean` and `Verification.lean` are the canonical project and axiom
entry points. The original snapshot manifest is preserved unchanged.

## Audit records and provenance

Original baseline build/audit records and mathematical reviews are retained.
The current verification overview above distinguishes those records from the
new focused source and kernel checks.

3,963 superseded generated build logs, execution results, and manifest copies
were removed from the working tree. They remain recoverable from
[the pre-cleanup commit](https://github.com/lixiang90/jsp168-hindman/tree/5dc91a1deaf73720b421f672009565e18f4e6dfa)
with `git show 5dc91a1deaf73720b421f672009565e18f4e6dfa:PATH`.
Proof sources, licenses, current verification, and all original 3,059 manifest
entries are unchanged by this cleanup.

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
