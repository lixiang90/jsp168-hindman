from pathlib import Path
import ast
import json
import re

prefix = "round-group-lie-nilpotency"
old_prefix = "round-native-bracket"
modules = [
    "Hindman168/NativeLieCommutatorDerivative.lean",
    "Hindman168/NativeLieCommutatorWords.lean",
    "Hindman168/LieLowerCentralProductCutoff.lean",
    "Hindman168/NativeLieCommutatorProducts.lean",
    "Hindman168/NativeLieGroupNilpotency.lean",
]

def replace_exact(text, before, after):
    assert text.count(before) == 1, before
    return text.replace(before, after)

register = Path(old_prefix + "-register.py").read_text(encoding="utf-8-sig")
register = replace_exact(register, '"round-adjoint-generator-audit.py"', '"round-native-bracket-audit.py"')
register = replace_exact(register, 'prefix = "round-native-bracket"', 'prefix = "' + prefix + '"')
register = register.replace('== 727', '== 733').replace(': 727', ': 733')
register = register.replace('== 29', '== 23').replace('== 27', '== 21').replace('"new_theorems": 27', '"new_theorems": 21')
start = register.index("modules = [")
end = register.index("\nnames = []", start)
register = register[:start] + "modules = " + json.dumps(modules, indent=4) + "\n" + register[end:]
Path(prefix + "-register.py").write_text(register, encoding="utf-8")
build = Path(old_prefix + "-build.py").read_text(encoding="utf-8-sig")
build = replace_exact(build, old_prefix, prefix)
Path(prefix + "-build.py").write_text(build, encoding="utf-8")

head = Path(old_prefix + "-audit.py").read_text(encoding="utf-8-sig").split("\nAPPLICATION =", 1)[0]
changes = {
    'PREFIX = "round-native-bracket"': 'PREFIX = "' + prefix + '"',
    'OLD = "round-adjoint-generator"': 'OLD = "round-native-bracket"',
    'len(baseline["files"]) == 727 and len(new_modules) == 6': 'len(baseline["files"]) == 733 and len(new_modules) == 5',
    'len(own) == 715 and len(pnt) == 9': 'len(own) == 720 and len(pnt) == 9',
    'len(names) == len(set(names)) == 29': 'len(names) == len(set(names)) == 23',
    'sum(c["theorems"] for c in module_counts.values()) == 27': 'sum(c["theorems"] for c in module_counts.values()) == 21',
    'len(registered) == len(set(registered)) == len(actual) == 3664': 'len(registered) == len(set(registered)) == len(actual) == 3687',
    'len(previous) == 3635': 'len(previous) == 3664',
    'len(source_files) == len({f["path"] for f in source_files}) == 733': 'len(source_files) == len({f["path"] for f in source_files}) == 738',
}
for before, after in changes.items():
    head = replace_exact(head, before, after)

application = [
    "PROGRESS: the preceding authoritative round was independently rechecked before proof edits. All 733 baseline source/configuration hashes are revalidated before registration. Retained proofs, StrongConjecture, dependencies and attribution remain byte-identical; only the root imports and exact-name axiom registry change among retained source/configuration files. No unavoidable blocker is established. The fixed local paper is compared to pinned Git objects; no remote or official updates are checked.",
    "NativeLieCommutatorDerivative constructs exactly the original group map c-g(x)=g*x*g-inverse*x-inverse. Actual multiplication is differentiated at the identity with its genuine two partial derivatives equal to identity. Differentiating the genuine identity c-g(x)*x=g*x*g-inverse then proves the actual original manifold derivative D c-g(1)=Ad-g-id. The commutator map's C-infinity regularity comes from original conjugation, multiplication and inverse. Native tangent aliases are reconciled with explicitly typed original model operators; there are no new source options, transparency or linter overrides.",
    "NativeLieCommutatorWords constructs actual right-nested words in the original group. Induction and the original subgroup commutator law prove each word of length k lies in the actual original group lower-central layer k. Original chart chain rules compute its derivative at the identity as the ordered product of actual adjoint differences. If that original layer is bottom, the genuine word is identically the original identity; its actual derivative is zero. This proves the product cutoff from original group nilpotency without assuming an adjoint-difference or bracket relation.",
    "NativeLieCommutatorProducts differentiates those genuinely vanishing products along the original native one-parameter curves, replacing one adjoint difference at a time by its actual derivative-defined generator. Constants stay in their original multiplication order, with no commutativity assumed. An induction over the number of replacements proves that every ordered product of k actual generators is zero under the original group lower-central cutoff k. Repeated equal parameters give the actual generator's kth power zero with the same cutoff.",
    "LieLowerCentralProductCutoff proves an algebraic implication for actual Lie modules: if every length-k ordered product of original toEnd actions vanishes, the original Lie lower-central series at k is bottom. The proof inducts through its actual linear span of brackets and places each preceding layer in the genuine kernel of every complementary action product. This lemma is actually instantiated in NativeLieGroupNilpotency, with products transported through the genuine continuous-to-linear ring homomorphism and the previously proved original generator=original native bracket identity.",
    "NativeLieGroupNilpotency proves original group lower-central termination at k implies original native Lie lower-central termination at the same k. In particular Group.IsNilpotent supplies native LieModule.IsNilpotent with cutoff at most the original group nilpotencyClass. No separately supplied native Lie-nilpotency premise remains in the public original-group finite adjoint formulas: both original adjoint curves and original exponential adjoints truncate at the original group nilpotencyClass, using the actual operator exponential and proved actual generator. The result applies to the arbitrary original Lie group, not a concrete matrix replacement. It does not identify individual group/Lie lower-central layers or construct a global exponential inverse.",
    "All five new modules, 21 proved theorems and two definitions are in the actual root and exact-name kernel registry, with 23 exact new selected declarations. Complete build and kernel processes terminate with zero exit codes; raw byte logs and hash records are retained. All new modules are warning-free and oleans current. All retained reports' exact axiom sets and six axiom-free declarations remain unchanged; only propext, Classical.choice and Quot.sound occur. Every one of 720 own and nine attributed PNT+ modules plus root and registry is scanned for executable trust bypasses. Dependencies and pins remain unchanged.",
    "Remaining: general native exponential differential formula, actual group/Lie lower-central layer identification, global inverse/BCH for arbitrary connected simply connected nilpotent Lie groups, faithful integration/Malcev comparison and arbitrary specified-lattice rational subgroup cocompactness. Nonabelian lattice logarithms are not assumed additive. Full calibration/Alignment and ordered positive arithmetic witness extraction remain unproved. StrongConjecture and the full prize target remain unproved; public repository creation, award PR and application await full formalization and audit.",
]
components = [
    "actual original group commutator identity derivative equals original adjoint minus identity, derived from actual multiplication and conjugation chain rules",
    "actual original nested group commutators lie in original group lower-central layers and have genuine derivatives equal to ordered adjoint-difference products",
    "original group lower-central termination forces every same-length ordered product of actual native bracket generators and same-cutoff powers to vanish by actual curve differentiation",
    "actual Lie-action product cutoff controls original Lie lower-central series through its genuine bracket span and actual complementary-product kernels",
    "original group nilpotency implies original native Lie-algebra nilpotency at the same cutoff, giving original native finite adjoint formulas at group nilpotencyClass without extra Lie-nilpotency premises",
]
progress = "The actual global linear equation identifies original adjoint curves and original exponential adjoints with genuine operator exponentials of their true derivative-defined generators. Original native chain rules identify the generators with the actual identity derivative of original adjoint; the genuine flow's mixed derivatives prove that their action equals the original native Lie bracket and their underlying linear maps equal original LieModule.toEnd. The actual original group commutator map now has proved native identity derivative Ad-g-id, derived from the genuine multiplication chain rule. Actual original nested commutator words have proved original group lower-central membership and derivatives equal to ordered actual adjoint-difference products. Original group lower-central termination makes each word identically identity and hence its derivative zero. Genuine differentiation along original native one-parameter curves replaces differences successively by actual bracket generators, proving that every same-length ordered generator product vanishes. The original Lie lower-central bracket-span definition and genuine operator kernels then show original native Lie lower-central termination at the same cutoff. Thus original Group.IsNilpotent now proves native LieModule.IsNilpotent without a supplied Lie-nilpotency premise. Actual original adjoint curves and exponential adjoints have finite formulas cut off at the original Group.nilpotencyClass. Individual group/Lie lower-central layer identification, the general native exponential differential formula, and global exponential invertibility/BCH still remain unproved."

body = Path(old_prefix + "-audit-body.py").read_text(encoding="utf-8-sig")
body = body[body.index("def record():"):]
changes = {
    'len(manifest["proved_components"]) == 802': 'len(manifest["proved_components"]) == 808',
    'len(manifest["proved_components"]) == 808 and manifest["proved_components"][-6:]': 'len(manifest["proved_components"]) == 813 and manifest["proved_components"][-5:]',
}
for before, after in changes.items():
    body = replace_exact(body, before, after)
numeric = {"727": "733", "27": "21", "29": "23", "715": "720", "724": "729", "3664": "3687"}
body = re.sub(r"\b(?:727|27|29|715|724|3664)\b", lambda m: numeric[m[0]], body)
body = replace_exact(body, '"new_module_count": 6', '"new_module_count": 5')
start = body.index("    note = (")
end = body.index('\n    Path("AUDIT.txt")', start)
note1 = "\n2026-10-10 round-group-lie-nilpotency: PROGRESS. Five new modules, 21 proved theorems and two definitions; 23 exact new reports. All 733 baseline source/config hashes revalidated before registration; only root and registry change among retained files. Genuine original commutator derivative is Ad-id. Actual nested original group commutators lie in original group lower-central layers and differentiate to ordered adjoint-difference products. Original lower-central termination and genuine successive native curve derivatives prove all same-length bracket-generator products vanish. Actual Lie lower-central bracket spans and genuine product kernels prove original native Lie termination at the same cutoff. Original Group.IsNilpotent now gives native LieModule.IsNilpotent, and actual original finite adjoint formulas use Group.nilpotencyClass without an additional Lie-nilpotency premise. No individual group/Lie layer identification or global inverse/BCH is supplied. Complete build terminal exit 0: "
note2 = " jobs. Kernel terminal exit 0: 3687 exact unique standard-axiom reports; all retained axiom sets and six axiom-free reports unchanged. Scanned 720 own and nine attributed PNT+ modules plus root/registry; 738 current source/config hashes. New modules warning-free and oleans current; fixed local paper objects match, no remote updates checked. General native dexp, group/Lie layer comparison, global inverse/BCH, specified-lattice transfer, full calibration/Alignment and StrongConjecture remain unproved. No unavoidable blocker. Review: round-group-lie-nilpotency-review.json.\n\n"
body = body[:start] + "    note = (" + repr(note1) + ' + str(verified["build_jobs"]) + ' + repr(note2) + ")" + body[end:]
assignments = "APPLICATION = " + repr(application) + "\n\nCOMPONENTS = " + repr(components) + "\n\nNEW_PROGRESS = " + repr(progress) + "\n\n\n"
assembled = head + "\n" + assignments + body
ast.parse(assembled)
Path(prefix + "-audit-body.py").write_text(assignments + body, encoding="utf-8")
Path(prefix + "-audit.py").write_text(assembled, encoding="utf-8")
