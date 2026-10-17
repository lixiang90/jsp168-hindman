# Audit mechanism self-test only

These tiny fixtures test the prepared verification mechanism on pinned Lean
4.32.2. They do **not** import, build, or verify `Hindman168.JSP000168`.
`ProbeModule.lean` deliberately declares unapproved private test axioms. These
isolated negative-test declarations are outside the proof target's import
closure. Never import these fixtures from any `Hindman168`, `OAI`, or
`PrimeNumberTheoremAnd` proof module.

Run explicitly in a new ignored directory:

```powershell
python verification/original-final-target/audit-self-test/run.py --output-dir verification-local/audit-self-test-new-run
```

The runner invokes installed Lean directly with `-j1 --trust=0
-DautoImplicit=false`; it never invokes Lake. It checks that a non-`module`
importer can enumerate a split module's unused private axiom and theorem, and
that `collectAxioms` finds private dependencies of exported theorems. The exact
canonical audit generator, with only the target/import name replaced, must
reject the fixture's unapproved private axiom (expected Lean exit 1).
That exit 1 means the checker correctly rejected the negative fixture; it is
not a passing result or verification evidence for JSP-000168.

The endpoint fixture checks the `endpointProposition (@theorem)`/`rfl` method
and confirms that explicit, implicit, and typeclass premises cannot be omitted
from its type lock. The dated report records actual fixture exits; it is no
evidence that the JSP target has compiled or passed its full axiom audit.

Source review of fixed Lean explains the split-file coverage:

- `Lean/Elab/Import.lean`, `processHeaderCore`: a file without a `module` header
  loads imports at `.private` level.
- `Lean/Environment.lean`, `importModulesCore`/`ImportedModule.mainModule?`:
  that level imports all dependencies' private data; `mkModuleData .private`
  retains every kernel constant, including prior exported/server constants.
- `moduleData.constNames` is the name list of those kernel constants;
  `extraConstNames` records code generator auxiliaries outside that kernel map.
- `Lean/Util/CollectAxioms.lean` uses cached transitive axiom data for exported
  declarations and traverses checked type/body data for remaining private ones.

Keep the generated audit as a non-`module` file. A successful source build,
actual 5,066-module audit, endpoint checks, source/artifact binding, and fresh
kernel replay remain separate requirements. No `public import` or additional
exposure option is needed for this existing non-`module` audit design.
