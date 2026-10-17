# Archived final verification evidence

Original result JSON and source/log bytes are preserved. Their historical verification-local paths are not rewritten; archive-index.json maps each original source path to its public archived file. Decompress gzip files before comparing their source SHA256/bytes. Gzip uses an empty stored filename and mtime 0.

The selected proof commit is 7ae70219fb4034899c6c2d23cc3b58ec6730a1ba. The all-declaration audit covers the actual local target closure; external unused declarations and external source rebuilding are outside that listing scope. Fresh replay uses Lean's own kernel for safe, nonpartial declarations. This is not an independent kernel or a claim of a cache-free rebuild. No award, first-proof, priority, authorship or payment determination is made.

Recorded tool copies preserve executed bytes; reproduce with the original repository paths and pinned inputs, rather than executing the archival copies at changed directory depths. The separate parser-recheck files record an actual Python-only archival gate, not another Lean run. The archive is incomplete whenever _INCOMPLETE exists.
