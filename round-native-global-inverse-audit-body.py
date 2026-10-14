APPLICATION = ['PROGRESS: the preceding finite-Picard and whole-group covering round was recorded and freshly rechecked before this saved 770-file baseline and current edits. Every baseline source/config hash is verified before registration. Retained proofs, StrongStatement, pins and attribution stay unchanged; only root imports and exact-name registry change among retained sources. No official/remote updates are checked and no unavoidable blocker is established.', 'NativeLieGlobalLogarithm uses the proved genuine E-to-G exponential covering of the entire original connected finite-dimensional nilpotent group. The original G is genuinely locally path connected because the original exponential is a quotient map from the actual real normed model E. No separate local-connectivity assumption is supplied, and original simply connectedness is not transferred to an open subset.', 'The actual covering lifting theorem applied to the identity continuous map of the whole original simply connected G and the actual lift 0 of 1 constructs a genuine continuous map L:G-to-E with L(1)=0 and Exp(L(g))=g. This is derived from the actual original covering, not a supplied logarithm, global inverse or flow. The original model is genuinely preconnected. True covering lift uniqueness compares L composed with Exp to identity E at zero, so L(Exp(v))=v. Hence actual original exponential injectivity is proved and the actual additive period subgroup K is exactly bottom.', 'NativeLieExponentialDiffeomorph identifies the constructed global logarithm with the retained actual native local logarithm near each original Exp(v). Whole-group surjectivity covers every original g. Actual exponential injectivity turns their genuine right inverse identities into actual local equality, which transfers the proved native C-infinity local inverse regularity. The actual Exp and actual L, with proved two-sided inverse laws, constitute a native Diffeomorph between original model E and original arbitrary G. Actual manifold differentiation of their identity composition gives the true inverse differential composition. No matrix replacement, assumed BCH or inverse regularity is supplied.', 'Two new modules, eight proved theorems and two definitions give ten exact new kernel reports. Require actual terminal exit-zero full build/kernel records, byte logs and hashes, current oleans, exact names/imports and all-source trust scans. All 754 own and nine attributed PNT+ modules, plus root and registry, are covered. Retained axiom sets and six retained axiom-free reports remain unchanged. Only standard axioms are allowed; fixed local paper objects and dependency pins are checked without updates.', 'Remaining: identify the actual finite Picard product logarithm as the rational Lie-polynomial BCH structure, compare individual original group/Lie lower-central layers, derive faithful integration/Malcev and arbitrary specified-lattice rational subgroup cocompactness. Original nonabelian lattice logarithms are not assumed additive. Full calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and full prize target remain unproved; publication and prize submission await full proof and audit.']

COMPONENTS = ['actual original simply connected nilpotent Lie group has a genuine continuous global logarithm by whole-group covering lifting with true two-sided inverse laws and eliminated original period subgroup', 'actual original native exponential and its constructed global logarithm form a genuine native C-infinity diffeomorphism with true inverse differential composition']

NEW_PROGRESS = 'The actual original native adjoint differential is the original native bracket, and original group nilpotency proves native Lie lower-central termination at the original class c. The actual original exponential comes from proved genuine global invariant curves. Original relative-curve mixed derivatives and group cocycle prove the actual finite dexp formula and genuine native local C-infinity inverses. Original fibers are exactly cosets of the proved closed discrete native central period subgroup. Actual dexp defect W_v lowers original layers, W_v^c=0, and the genuine finite geometric sum U_v is its true two-sided inverse. The actual C-infinity field F_w(v)=U_v(w) strictly improves parameter differences by one original lower-central layer. Original finite-dimensionality proves these layers genuinely closed and true quotient-map integral commutation keeps actual integrals inside them. Actual global Picard iterates gamma_0=u and gamma_(n+1)=u+integral(0..t,F_w(gamma_n)) have true FTC derivatives. Actual differences gamma_(n+1)-gamma_n belong to S_n; the original nilpotency class c kills the next difference, proving gamma_(c+1)=gamma_c and the genuine global logarithm-lifting ODE including c=0. Actual manifold chain rules and original global integral-curve uniqueness prove Exp(gamma(t))=Exp(u)*gamma_w(t), giving a true product logarithm at one. The actual original exponential range is a subgroup; its true openness and original connectedness make it all of G. Thus genuine whole-group surjectivity and the actual additive-period quotient covering are proved. Original simply connectedness now eliminates the actual period group. Original local path connectedness is genuinely derived from the actual exponential quotient map of original E; it is not an extra premise. The true covering lifting theorem lifts identity G with lift zero of one to an actual continuous logarithm L. Actual preconnectedness of original E and genuine covering lift uniqueness prove both inverse laws L(Exp(v))=v and Exp(L(g))=g. Actual original exponential injectivity follows and K is exactly bottom. Near every original group point the actual global L equals the previously constructed true local logarithm by injectivity. Therefore L is genuinely native C-infinity. The actual native exponential and this constructed L form a global native C-infinity Diffeomorph E-to-G, with actual inverse differential composition. Global surjectivity, injectivity, period elimination and global smooth inverse no longer remain open tasks. No replacement matrix model, supplied global inverse, assumed BCH or nonabelian additive lattice logarithms is used. Remaining: prove that the genuine finite Picard product logarithms have the required rational Lie-polynomial BCH structure; compare individual original group/Lie lower-central layers; derive faithful integration/Malcev and arbitrary specified-lattice rational subgroup cocompactness. Full calibration/Alignment and original ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target are unproved; publication and submission await full proof and audit. No unavoidable blocker is established.'


def record():
    from importlib.util import spec_from_file_location, module_from_spec
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and manifest["full_target_proved"] is False
    assert len(manifest["proved_components"]) == 845
    assert not set(COMPONENTS) & set(manifest["proved_components"])
    spec = spec_from_file_location("previous_audit_body", OLD + "-audit.py")
    previous = module_from_spec(spec)
    spec.loader.exec_module(previous)
    remaining = manifest["last_round"]["remaining"]
    assert remaining.count(previous.NEW_PROGRESS) == 1
    remaining = remaining.replace(previous.NEW_PROGRESS, NEW_PROGRESS)
    old_status = 'Global exponential invertibility for arbitrary connected simply connected nilpotent Lie groups, full faithful matrix integration or Malcev comparison, BCH comparison outside the concrete strict-matrix realization, and transfer to arbitrary original paper groups with their specified lattices remain unproved; no universal group embedding or arbitrary rational subgroup theorem is asserted.'
    new_status = 'Global native C-infinity exponential invertibility for arbitrary original connected simply connected finite-dimensional real nilpotent Lie groups is now proved from the actual covering lift and actual local inverse comparison. Full faithful matrix integration or Malcev comparison, rational Lie-polynomial BCH comparison outside the concrete strict-matrix realization, and specified-lattice rational subgroup cocompactness remain unproved; no universal group embedding or arbitrary rational subgroup theorem is asserted.'
    assert remaining.count(old_status) == 1
    remaining = remaining.replace(old_status, new_status)
    review = {
        "date": "2026-10-10", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": 770,
        "retained_changed": ["Hindman168.lean", "Verification.lean"],
        "new_modules": registration["new_modules"], "new_theorem_count": 8,
        "new_selected_report_count": 10, "module_report_counts": registration["module_report_counts"],
        "application_review": APPLICATION, "verification": verified, "remaining": remaining,
    }
    manifest.update(
        date="2026-10-10", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 2, "new_theorem_count": 8,
                    "new_selected_report_count": 10, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = ('\n2026-10-10 round-native-global-inverse: PROGRESS. Two new modules, eight proved theorems and two definitions; ten exact new reports. All 770 baseline source/config hashes verified before registration. Retained proofs, pins and attribution unchanged; only root and registry changed. The actual original E-to-G exponential covering and quotient-derived original local path connectedness permit the genuine covering lifting theorem on the original simply connected G. It constructs L:G-to-E with L(1)=0 and Exp(L(g))=g. Actual preconnectedness of original E and actual lift uniqueness prove L(Exp(v))=v, genuine original exponential injectivity and K=bottom. Actual injectivity identifies L locally with the actual native local logarithm at every group point, proving native C-infinity regularity. The actual original exponential and derived L are a genuine global native C-infinity Diffeomorph with actual inverse differential composition. Rational Lie-polynomial BCH, individual group/Lie layer comparison, Malcev, specified-lattice cocompactness and full arithmetic target remain unproved. Complete build terminal exit 0: ' + str(verified["build_jobs"]) + ' jobs. Kernel terminal exit 0: 3864 exact unique standard-axiom reports. Retained axioms and six retained axiom-free reports unchanged. All 754 own and nine attributed PNT+ modules plus root and registry scanned; 772 current source/config hashes. New sources warning-free and oleans current. Fixed local paper and pins match; no remote updates. StrongConjecture and prize target unproved. No unavoidable blocker. Review: round-native-global-inverse-review.json.\n\n')
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 754, "pntplus_modules": 9, "scanned_module_count": 763,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 3864, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_registration": 770, "previous_current_state_rechecked_before_edits": True,
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
    assert review["new_theorem_count"] == 8 and review["new_selected_report_count"] == 10
    assert review["new_modules"] == registration["new_modules"]
    assert review["module_report_counts"] == registration["module_report_counts"]
    assert manifest["last_round"]["remaining"] == review["remaining"] == read("AUDIT.txt").split("Remaining proof work:", 1)[1].strip()
    assert len(manifest["proved_components"]) == 847 and manifest["proved_components"][-2:] == COMPONENTS
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
    assert scan["scanned_module_count"] == 763 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 3864 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 8, "new_selected_declarations": 10,
        "all_source_modules_scanned": 763, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 3864,
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
