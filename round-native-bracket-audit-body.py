APPLICATION = [
    "PROGRESS: the preceding authoritative round was independently rechecked before proof edits. All 727 retained source/configuration hashes are verified before registration. Only the root imports and exact-name kernel registry change among retained files; retained proof sources, StrongConjecture, attribution and dependency pins are byte-identical. No unavoidable blocker is established. The fixed local paper is compared with pinned Git objects, with no remote or official update check.",
    "NativeLieCoordinateBracket uses the actual inverse identity-chart pullback of each original native invariant field. The actual boundaryless identity point proves range and target are neighborhoods, without globally declaring the model range universal. Genuine two-sided chart derivative identities prove the actual coordinate field value and regularity. Unfolding the original GroupLieAlgebra bracket and the genuine vector-field pullback definition gives the original bracket as DW(w-field) applied to v minus DV(v-field) applied to w.",
    "MixedFlowJacobian proves the real mixed time/state derivative identity for an actual C2 map from time times state: the genuine derivative of fderiv f, actual chain rules and symmetry of its actual second derivative identify the time derivative of its spatial Jacobian with the spatial derivative of its proved zero-time velocity. This analytic lemma is instantiated in NativeLieRightCoordinateFlow with the actual original flow, all regularity and velocity premises proved from original smooth multiplication and actual native curves.",
    "NativeLieRightCoordinateFlow is exactly chart(symm-chart(z)*gamma-v(t)). Native integral-curve and chart chain rules prove its actual coordinate ODE and C-infinity regularity near the identity. NativeLieRightFlowTransport derives its spatial derivative from the original inverse chart and original right translation. The actual previously proved right-translation pushforward proves the eventual transport equation DF(t,z0)(0,Ad(gamma-v(t))w)=W-w(F(t,z0)). Native tangent aliases are normalized locally before normed derivatives; there are no transparency, linter or heartbeat overrides.",
    "NativeLieAdjointInfinitesimal first proves the actual zero-time spatial derivative is identity from the actual chart inverse law on a genuine neighborhood. Differentiating the original transport identity uses actual Jacobian variation, actual adjoint action derivative and the actual coordinate ODE. Derivative uniqueness gives DV(z0)w+B-v(w)=DW(z0)v, so the genuine derivative-defined generator action equals the original native Lie bracket. There is no assumed generator, flow, derivative, BCH formula or bracket compatibility replacing this proof.",
    "NativeLieNilpotentAdjoint identifies the actual generator's underlying linear map with the original LieModule.toEnd. Under an explicit LieModule.IsNilpotent instance for the original GroupLieAlgebra, its original lower-central series supplies one common power cutoff for every actual generator, hence genuine operator nilpotency. The actual Banach exponential series truncates beyond that cutoff, proving a uniform finite formula for the original adjoint curves and a finite formula for the original exponential's adjoint. No group-to-Lie nilpotency or lower-central comparison is asserted; the explicit native Lie-algebra premise remains visible.",
    "All six modules, 27 proved theorems and two definitions, with 29 exact unique new names, are included in the actual root and registry. Complete build and kernel processes terminate with exit code zero; raw byte logs and SHA-256 records are retained. All new oleans are current and all modules warning-free. Every retained report's axiom set and six axiom-free declarations are unchanged. All 715 own and nine attributed PNT+ modules plus root and registry are scanned for executable trust bypasses. All selected reports use only propext, Classical.choice and Quot.sound.",
    "Next prove native group/Lie lower-central comparison and the original native exponential differential formula, then global inverse/BCH for arbitrary connected simply connected nilpotent Lie groups and the arbitrary specified-lattice rational subgroup cocompactness transfer. Nonabelian lattice logarithms are not assumed additive; concrete matrix results are not substituted for the original arbitrary groups. Full calibration/Alignment and ordered positive arithmetic witness extraction remain unproved. StrongConjecture remains unproved; public repository creation, award PR and prize application await complete formalization and audit.",
]

COMPONENTS = [
    "actual inverse identity-chart invariant coordinate fields and original native Lie bracket identified with their genuine coordinate derivative difference",
    "actual mixed time/state Jacobian derivative from genuine C2 second-derivative symmetry, instantiated with the original native right-translation coordinate flow",
    "actual native right-translation coordinate flow C-infinity and original ODE, with actual spatial derivative transporting adjoint to original coordinate invariant field",
    "actual derivative-defined native adjoint generator action equals the original native Lie bracket by differentiation of genuine original flow transport",
    "actual native adjoint generator underlying linear map equals original LieModule.toEnd, with uniform vanishing powers derived under original native Lie-algebra nilpotency",
    "actual original adjoint curves have a uniform finite exponential formula under original native Lie-algebra nilpotency, with an actual finite formula for native exponential adjoint",
]

NEW_PROGRESS = "The actual global linear equation proves that original adjoint curves and original exponential adjoints equal genuine operator exponentials of their derivative-defined generators. Actual native chain rules identify each generator with the genuine identity derivative of original adjoint, with parameter linearity, continuous alternating action, original equivariance, Leibniz and commutator identities. Actual original right-translation derivatives have genuine inverse and invariant-field transport formulas. The original identity-chart invariant coordinate fields are now proved smooth and express the original native Lie bracket by their actual derivative difference. The genuine right-translation coordinate flow has its actual C-infinity regularity, coordinate ODE and spatial adjoint transport; true mixed second derivatives prove its Jacobian time variation. Differentiating that actual transport identity now proves B-v(w) equals the original native Lie bracket. The generator's actual underlying linear map equals original LieModule.toEnd. Under the explicit original GroupLieAlgebra LieModule.IsNilpotent premise, the actual lower-central series gives uniform generator nilpotency and the actual operator exponential truncates to a uniform finite formula for original adjoint curves and exponential adjoints. Native group/Lie lower-central and nilpotency comparison and the general native exponential differential formula remain unproved; group nilpotency alone is not asserted to supply the explicit native Lie-algebra premise."


def record():
    from importlib.util import spec_from_file_location, module_from_spec
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and manifest["full_target_proved"] is False
    assert len(manifest["proved_components"]) == 802
    assert not set(COMPONENTS) & set(manifest["proved_components"])
    spec = spec_from_file_location("previous_audit_body", OLD + "-audit.py")
    previous = module_from_spec(spec)
    spec.loader.exec_module(previous)
    remaining = manifest["last_round"]["remaining"]
    assert remaining.count(previous.NEW_PROGRESS) == 1
    remaining = remaining.replace(previous.NEW_PROGRESS, NEW_PROGRESS)
    review = {
        "date": "2026-10-10", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": 727,
        "retained_changed": ["Hindman168.lean", "Verification.lean"],
        "new_modules": registration["new_modules"], "new_theorem_count": 27,
        "new_selected_report_count": 29, "module_report_counts": registration["module_report_counts"],
        "application_review": APPLICATION, "verification": verified, "remaining": remaining,
    }
    manifest.update(
        date="2026-10-10", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 6, "new_theorem_count": 27,
                    "new_selected_report_count": 29, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = ("\n2026-10-10 round-native-bracket: PROGRESS. Six new modules, 27 proved theorems and two definitions; 29 exact new kernel reports. All 727 baseline hashes verified before registration; previous authoritative round independently rechecked before edits. Only root and registry changed among retained source/config files. Original native identity-chart invariant fields and bracket coordinate derivatives proved. Actual C2 mixed differentiation and genuine native right-coordinate flow ODE prove spatial Jacobian variation and original adjoint transport. Differentiation identifies the actual adjoint generator action with the original native Lie bracket. Its underlying linear map equals the original toEnd. An explicit native LieModule.IsNilpotent premise gives uniform actual generator cutoff and genuine finite adjoint exponential formulas; original group/Lie nilpotency comparison is not supplied. Complete build terminal exit 0: " + str(verified["build_jobs"]) + " jobs. Kernel terminal exit 0: 3664 exact unique standard-axiom reports; every retained axiom set and six axiom-free reports unchanged. Scanned 715 own and nine attributed PNT+ modules plus root/registry; 733 current source/configuration hashes. New modules warning-free, oleans current; fixed local paper objects match, no remote update checks. General native dexp, group/Lie lower-central comparison, global inverse/BCH and arbitrary specified-lattice transfer, full calibration/Alignment and StrongConjecture remain unproved. No unavoidable blocker. Review: round-native-bracket-review.json.\n\n")
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 715, "pntplus_modules": 9, "scanned_module_count": 724,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 3664, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_registration": 727, "previous_current_state_rechecked_before_edits": True,
        "retained_changed": review["retained_changed"], "retained_proof_sources_unchanged": True,
        "pins_and_attributed_sources_unchanged": True, "root_imports_exact": True,
        "registered_names_exact": True, "kernel_names_exact": True,
        "full_target_proved": False, "verified": verified,
    })
    print(json.dumps({"recorded": True, "verified": verified, "proved_components": len(manifest["proved_components"])}))


def recheck():
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    review = obj(PREFIX + "-review.json")
    result = obj(PREFIX + "-checks.json")
    assert manifest["files"] == files and all(digest(f["path"]) == f["sha256"] for f in files)
    assert review["verification"] == result["verified"] == verified
    assert review["new_theorem_count"] == 27 and review["new_selected_report_count"] == 29
    assert review["new_modules"] == registration["new_modules"]
    assert review["module_report_counts"] == registration["module_report_counts"]
    assert manifest["last_round"]["remaining"] == review["remaining"] == read("AUDIT.txt").split("Remaining proof work:", 1)[1].strip()
    assert len(manifest["proved_components"]) == 808 and manifest["proved_components"][-6:] == COMPONENTS
    assert manifest["full_target_proved"] is False and manifest["build_succeeded"] and manifest["axiom_check_succeeded"]
    assert obj(PREFIX + "-preprint-local-check.json") == fixed
    assert manifest["build_log"] == PREFIX + "-build.txt" and manifest["axiom_log"] == PREFIX + "-axioms.txt"
    for key, value in {
        "build_job_count": verified["build_jobs"], "hindman_module_count": verified["project_modules"],
        "pntplus_module_count": verified["pntplus_modules"], "selected_axiom_report_count": verified["axiom_reports"],
        "source_scan_module_count": verified["source_scan_modules"],
    }.items():
        assert manifest[key] == value
    assert Path("BUILD-EVIDENCE.txt").read_bytes() == b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n"
    scan = obj(PREFIX + "-source-scan.json")
    assert scan["scanned_module_count"] == 724 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 3664 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 27, "new_selected_declarations": 29,
        "all_source_modules_scanned": 724, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 3664,
        "new_oleans_current": True, "root_imports_exact": True, "source_theorem_names_match_registration": True,
        "allowed_standard_axioms_only": True, "retained_axiom_sets_unchanged": True, "combined_logs_exact": True,
        "review_audit_manifest_remaining_agree": True, "lean_actual": fixed["lean_actual"],
        "mathlib_actual": fixed["mathlib_actual"], "pntplus_actual": fixed["pntplus_actual"],
        "fixed_local_preprint_objects_match": True, "remote_updates_checked": False, "full_target_proved": False,
    }
    write_obj(PREFIX + "-checks.json", result)
    print(json.dumps(result["fresh_final_recheck"], ensure_ascii=False, indent=2))


if __name__ == "__main__":
    assert len(sys.argv) == 2 and sys.argv[1] in {"record", "recheck"}
    (record if sys.argv[1] == "record" else recheck)()
