# Travel continuation — unfinished joint restriction

This private working branch preserves all three source files that were not yet
committed at the travel-backup checkpoint on 2026-10-14.

## Branches and verification status

- `main`, commit `e5e45b1e1227a8df34ee95eadd4b8d87b4811c74`, is the latest
  fully audited checkpoint (`round-native-standard-face-haar`). Its 3059 exact
  manifest hashes were rechecked successfully before this backup.
- `wip/joint-restriction` adds the three unfinished source files and this note.
  These additions are **not** covered by that audit or registered in the root
  imports / `Verification.lean`. Passing the existing snapshot hash check does
  not validate these new files.
- `Hindman168.StrongConjecture` remains unproved. Keep the repository private.
  No public release, PR or prize application has been made.

## Resume on another computer

Follow README.md to install the pinned dependencies. To resume this draft:

```sh
git clone https://github.com/lixiang90/jsp168-hindman.git
cd jsp168-hindman
git switch wip/joint-restriction
lake exe cache get
lake build Hindman168.AlignmentRestrictedCubeComparison
```

The last command currently fails at the restriction identity described below.
For the audited checkpoint instead, use `git switch main`, then the verification
commands in README.md. Do not run `lake update` or change the pinned toolchain.

## Exact current work

1. `Hindman168/NativeFinitePiCosetRestriction.lean`: compiled successfully.
   Constructs restriction of a full finite product quotient to a selected
   subfamily, proves coordinate identities and continuity, and defines the
   corresponding restricted cube projection. Not yet included in a full audit.
2. `Hindman168/AlignmentOriginalJointRestriction.lean`: unfinished.
   A fresh `lake env lean -DautoImplicit=false` check failed at line 24 with an
   unsolved coordinate equality in `alignment_original_joint_point_restriction`.
   After applying the coset homeomorphism's injectivity and `funext k`, the
   `simp only` list does not reduce the two homeomorphism applications. The next
   task is to expose their coordinate maps explicitly and use the existing
   restriction and original-orbit component identities. No `sorry` was inserted.
   The real-source integer restriction theorem depends on this identity.
3. `Hindman168/AlignmentRestrictedCubeComparison.lean`: draft comparison of the
   full heterogeneous source through a subfamily projection. Its dependency
   fails first, so this file has not yet been validated. Fix the restriction
   identity, then check its final `simpa` against the fixed-target comparison.

## Mathematical next steps

Continue from `STANDARD-FACE-HAAR-CONTINUATION.txt` and `CURRENT-STATUS.txt`.
The immediate objective is all target marginals of ONE heterogeneous joint
source. Use the new restricted full-cube comparison with
`native_projected_cube_empirical_invariance`, taking its source to be the FULL
joint nilmanifold and its target to be the selected subfamily quotient.

Extract the full source's subsequence, subgroup filtration, period, rational
representatives and smooth curve once. All target marginals must retain those
same witnesses. Do not apply the fixed-target existence theorem separately and
identify its independently chosen witnesses. Secure all countable good
conditions before selecting the period; the existing all-target selection
theorem is the foundation for the heterogeneous selection step.

Then establish actual homeomorphisms and apply the full-support bridge to obtain
setwise invariance. Joint lifts, full Alignment, the remaining arbitrary-input
GTZ inverse theorem and the final same-color FS/FP argument remain outstanding.
File counts do not provide a reliable completion percentage or time estimate.

After repairing these drafts, register the new modules and axiom reports and
run the usual full build, source/axiom audit and hash verification before
promoting them into a new audited main checkpoint.
