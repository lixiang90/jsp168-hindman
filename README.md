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
- `CUBE-BINOMIAL-CONTINUATION.txt`: detailed latest interfaces and next proof step.
- `CUBE-CHARACTER-CONTINUATION.txt`: preceding character construction checkpoint.
- `AUDIT.txt` and `round-*-review.json`: accumulated mathematical reviews.
- `Hindman168.lean`: canonical project imports.
- `Verification.lean`: registered axiom checks.

The latest mathematical round is `round-cube-binomial-coefficient`; consult
`CURRENT-STATUS.txt` and the manifest for its terminal audit result. It proves
the actual Boolean binomial expansion, the isolated coefficient with its
factorial denominator, and no cancellation in the explicit scalar Taylor/face
sum. Instantiating that sum with the original Taylor coefficients and actual
residue-cube horizontal functional gives coefficient escape.

The next task is to identify that explicit scalar sum with the horizontal
projection of the actual group-valued cube, and prove original cube-polynomial
adaptation. Simultaneous local cube laws, Alignment, the remaining GTZ inverse
work and the final same-color FS/FP argument are still outstanding.

Continue from the same original source, final subgroup filtration and
original nilpotency bound. Do not replace the target with a weaker result,
assume a source/Haar/character/inverse oracle, introduce `sorry` or new
axioms, or claim the anticipated scalar is a polynomial coefficient before
proving that identity.

## Audit records and provenance

Existing round scripts and logs preserve the original workstation evidence.
Some historical scripts refer to Windows paths, the local pinned OpenAI
paper checkout, and a local PNTPlus checkout. They are archival author-audit
tools, not portable installation scripts. Use `scripts/verify_snapshot.py`
for the portable checkpoint check; consult the round review before adapting
an old audit script on a new machine.

`work-in-progress/` and root-level scratch files are retained for continuity;
they are not automatically part of the canonical build or a claim of proof.

The paper source is pinned to OpenAI/math commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Dependency attribution and licenses are preserved in `PNTPLUS-ATTRIBUTION.txt`,
`LICENSE-PNTPLUS`, and `dependencies/openai-finite-szemeredi/`.
No new blanket license is assigned to the project's original contributions
by this checkpoint upload.
