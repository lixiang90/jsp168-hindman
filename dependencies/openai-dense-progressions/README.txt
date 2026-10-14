OpenAI dense-progression candidate, isolated verification only.
Source: https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean
Copyright/authorship: original OpenAI contributors; Apache-2.0 (LICENSE copied).
Original source toolchain is Lean 4.34.1. This candidate ports APIs and proofs
against this project's pinned Lean 4.32.2 / mathlib, without changing main pins.
Immutable originals and exact compatibility edits are retained in the manifest
and port script. The mathematical statements and assumptions must be preserved.
No comparator challenge or sorry module is copied. No dependency is imported
into Hindman168. Source manifests/hashes and later compatibility edits must be
retained and attributed. A source scan or partial build is NOT proof verification.
Require terminal full selected build, original semantic review and transitive
standard-only axiom audit before treating the result as a usable dependency.
Supplemental mathlib exterior-power source is by Justus Springer, Apache-2.0,
at commit d13f23b723b8a846827a245b89c10fc7d3f11612. Its isolated compatibility
module must also be compiled and audited before use. This is attributed code.
