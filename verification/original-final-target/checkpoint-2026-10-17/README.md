# Partial final verification checkpoint — 2026-10-17

Selected proof source: `7ae70219fb4034899c6c2d23cc3b58ec6730a1ba`.

The complete explicit `Hindman168.JSP000168` build returned actual Lake exit 0 and source-bound wrapper exit 0. Endpoint exact-type checks and the all-local-declaration transitive-axiom audit returned actual exit 0. The supplied complete parser report covers all 5,066 modules, 70,418 records and 70,306 unique names, with only propext, Classical.choice and Quot.sound observed.

**Fresh kernel replay was still running when this checkpoint was captured. The whole final suite and final before/after artifact comparison are incomplete here. This checkpoint does not announce a final verified release, public visibility, awards PR, priority or award acceptance.** A later completed report must supersede this snapshot.

[checkpoint-index.json](checkpoint-index.json) records original and stored bytes/SHA256. Logs ending `.gz` use gzip with mtime 0 and an empty filename; decompress before checking raw source hashes. Original result paths remain verbatim. [suite/running-snapshot.json](suite/running-snapshot.json) is a fixed copy of the running journal, not a live status feed. The full before-artifact inventory is not archived by this partial checkpoint; its eventual comparison belongs to the final suite.

Proof source/tool manifest and generated audit are under [prepared](prepared/source-closure.json), actual whole build records under [build](build/result.json), endpoint output at [01.log](suite/01.log), full declaration output at [02.log.gz](suite/02.log.gz), and its [scope parser summary](prepared/audit-summary.json). The [raw Git byte report](raw-git-binding.json) concerns the selected proof commit. [Contribution evidence](contributions.md) is a separately dated source-history report retaining its own limits and original status text.

The declaration listing covers the local closure including private/internal declarations and their transitive axiom dependencies. It does not enumerate unused external declarations or claim an external-source rebuild. Fresh replay uses the same pinned Lean kernel on safe, nonpartial declarations. The successful build used incremental artifacts and pinned official caches.
