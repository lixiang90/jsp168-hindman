APPLICATION = ['PROGRESS: the original center positive-root round was independently rechecked before these edits. All 866 baseline source/config hashes were verified before registration. Only retained root and registry change. Retained original Lie group proofs, specified lattice, StrongStatement, pinned Lean/Mathlib/PNT+ and attributed sources are unchanged. No remote updates.', 'FiniteCentralQuotientCommutator proves genuine commutators are unchanged by actual central right multipliers in either variable. Actual equality in the original center quotient gives equality of commutators. Representatives of an actually finite center quotient give a finite set containing all actual commutator values, and the retained Mathlib Schur theorem gives a finite actual commutator subgroup. No finite commutator hypothesis replaces this step.', 'FiniteTorsionGenerators uses the actual finite generator set and its genuine subgroup closure. Actual generator images in the genuine abelianization lie in its torsion subgroup; closure and genuine quotient surjectivity prove the entire abelianization torsion. Actual finite generation plus the retained finite-abelian-group theorem give finite abelianization. A finite actual commutator kernel then gives finite original group by the actual kernel/range finiteness theorem.', 'NilpotentTorsionClosure uses the genuine Group.nilpotent_center_quotient_ind for arbitrary original nilpotent groups. The actual center quotient images of the specified finite-order generators generate a finite subgroup by induction. Restriction of the actual quotient map to their original generated subgroup has finite actual range and central kernel. Genuine finite-index monotonicity gives finite actual center quotient of that subgroup; the proved Schur step and finite abelianization give its finiteness. A finitely generated nilpotent torsion group is consequently finite, and applying the original finite-generated-subgroup theorem to two finite-order elements proves multiplication closure without assuming commutativity.', 'NilpotentPositiveRoots constructs the actual finite-order normal subgroup with proved noncommutative multiplication closure, actual inverses and the genuine conjugation power identity. For a specified NORMAL subgroup, the inverse image of this subgroup under the actual quotient map equals the positive root set exactly. This gives genuine noncommuting root multiplication, a normal root subgroup and root closure. Its actual quotient has no nonidentity finite-order element.', 'For a finitely generated actual subgroup K inside those roots of the specified NORMAL subgroup Gamma, the actual K/(Gamma intersect K) is finitely generated, nilpotent and torsion. The newly proved finiteness theorem applies, and the actual finite quotient exponent gives one positive natural power sending EVERY element of K back to the original Gamma. This is an existence result for a uniform denominator in this normal setting; no explicit numerical bound or claim for nonnormal lattices is made.', 'Four new modules, seventeen proved theorems, two subgroup definitions and one normality instance give twenty exact new kernel reports. Actual full build and exact kernel checks cover all 852 own and nine attributed PNT+ sources plus root/registry. Actual source/config hashes, retained axiom sets, empty-report sets, new current oleans and warning-free logs are checked. No options, proof placeholders, added axioms or dependency edits.', 'Application boundary: the original specified lattice Gamma is not assumed normal in its ambient original nilpotent Lie group. The new generic normal-subgroup results may be applied inside genuine subgroup quotients only when normality is proved. They do not supply general nonnormal root multiplication, full hull-to-Gamma powers or the central W-kernel equality. Fixed local paper Section 07 lines 13-20 still requires the arbitrary original group and specified lattice. Full original rational-form induction, arbitrary rational subgroup cocompactness, quantitative bounds, reverse group/Lie lower-central comparison, Malcev, Calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target remain unproved. Publication and submission await full proof/audit. No unavoidable blocker.']

COMPONENTS = ['actual finite center quotient gives finite actual commutator subgroup by central multiplier invariance, finite representatives and genuine Schur theorem', 'actual finite torsion generator set gives finite actual abelianization and finite original group when the actual commutator subgroup is finite', 'actual finite-order generators in any original nilpotent group generate a finite subgroup by genuine center-quotient induction, giving finite-generation torsion finiteness and noncommuting torsion multiplication', 'actual roots of a specified normal subgroup form a genuine normal subgroup with torsion-free quotient, and every finitely generated subgroup of those roots has a finite intersection quotient and one uniform positive power in the original specified subgroup']

NEW_PROGRESS = 'Retained original native Exp/Log diffeomorphism, rational finite BCH/Picard construction, W bracket closure, full real log span and actual specified lattice Gamma finite generation remain proved. The actual center lattice has discrete full integer/rational/real log spans and compact additive quotient; its rational exponential hull is exactly the actual central positive roots of Gamma. The original center quotient has a constructed genuine smooth Hausdorff simply connected LieGroup, discrete cocompact image lattice and strictly lower real model dimension. Its actual differential is pi with kernel V; pi preserves genuine brackets and intertwines actual native Exp/Log, mapping original W=span_Q Log Gamma exactly onto the actual projected subgroup rational log span. Now generic genuine center-quotient induction, finite center quotient commutators via Schur, and finite abelianization prove finite-order generators in any nilpotent group generate a finite subgroup. Thus actual torsion elements form a normal subgroup without a commutativity assumption. For a genuinely normal specified subgroup only, actual positive roots form a normal subgroup, its quotient has no nontrivial torsion, and every actual finitely generated subgroup inside those roots has a finite intersection quotient and one uniform positive power in the original subgroup. The actual prize lattice Gamma is not assumed normal, and these normal-case results do not replace the required general proof. Remaining: general nonnormal root multiplication and full rational hull-to-Gamma positive powers; identify W(Gamma) intersect V with the actual specified center rational log span; finish full original ambient scalar-extension injectivity and specified-lattice rational-form induction; arbitrary specified-lattice rational subgroup cocompactness; quantitative degree/denominator bounds; reverse group/Lie lower-central comparison and algebraic layer closedness; faithful integration/Malcev. Full Calibration/Alignment, ordered positive arithmetic witnesses, StrongConjecture and the full prize target remain unproved. Publication and submission await full proof/audit. No unavoidable blocker.'


def record():
    from importlib.util import spec_from_file_location, module_from_spec
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and manifest["full_target_proved"] is False
    assert len(manifest["proved_components"]) == 941
    assert not set(COMPONENTS) & set(manifest["proved_components"])
    spec = spec_from_file_location("previous_audit_body", OLD + "-audit.py")
    previous = module_from_spec(spec)
    spec.loader.exec_module(previous)
    remaining = manifest["last_round"]["remaining"]
    assert remaining.count(previous.NEW_PROGRESS) == 1
    remaining = remaining.replace(previous.NEW_PROGRESS, NEW_PROGRESS)
    review = {
        "date": "2026-10-10", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": 866,
        "retained_changed": ["Hindman168.lean", "Verification.lean"],
        "new_modules": registration["new_modules"], "new_theorem_count": 17,
        "new_selected_report_count": 20, "module_report_counts": registration["module_report_counts"],
        "application_review": APPLICATION, "verification": verified, "remaining": remaining,
    }
    manifest.update(
        date="2026-10-10", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 4, "new_theorem_count": 17,
                    "new_selected_report_count": 20, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = '\n2026-10-10 round-nilpotent-torsion: PROGRESS. Four new modules, seventeen proved theorems, two definitions and one normality instance; twenty exact new reports. All 866 baseline hashes verified before registration; only retained root/registry change. Actual central quotient commutator representatives and genuine Schur theorem prove finite commutator subgroup for finite actual center quotient. Actual finite torsion generator set gives finite actual abelianization. Genuine center quotient induction gives finite subgroup generated by any actual finite set of finite-order elements in any nilpotent group; thus finite-generation torsion finiteness and noncommuting torsion multiplication. Actual torsion elements form a normal subgroup. For a genuinely NORMAL specified subgroup its actual root set is the inverse image of actual quotient torsion, hence a normal root-closed subgroup with no nontrivial torsion in the remaining quotient. Each finitely generated subgroup inside those normal roots has finite actual intersection quotient and one common positive power landing in the original subgroup. The actual prize lattice is not assumed normal. General nonnormal roots, full hull-to-lattice powers, W-center kernel equality, full original rational-form induction, arbitrary rational subgroup cocompactness, quantitative bounds, reverse group/Lie comparison, Malcev and full target remain unproved. All retained axiom sets and eleven retained axiom-free reports unchanged; new exact reports have no empty axiom sets. All 852 own and nine attributed PNT+ modules plus root/registry scanned; 870 source/config hashes. Actual full build and exact kernel totals: ' + str(verified["build_jobs"]) + ' jobs, 4210 exact unique allowed-standard-axiom reports, both terminal exit 0. New sources warning-free and oleans current. Actual pins and fixed local paper match; no remote updates. No unavoidable blocker. Review: round-nilpotent-torsion-review.json.\n\n'
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 852, "pntplus_modules": 9, "scanned_module_count": 861,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 4210, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
        "retained_axiom_free_reports": sorted(AXIOM_FREE - NEW_AXIOM_FREE),
        "new_axiom_free_reports": sorted(NEW_AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_registration": 866, "previous_current_state_rechecked_before_edits": True,
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
    assert review["new_theorem_count"] == 17 and review["new_selected_report_count"] == 20
    assert review["new_modules"] == registration["new_modules"]
    assert review["module_report_counts"] == registration["module_report_counts"]
    assert manifest["last_round"]["remaining"] == review["remaining"] == read("AUDIT.txt").split("Remaining proof work:", 1)[1].strip()
    assert len(manifest["proved_components"]) == 945 and manifest["proved_components"][-4:] == COMPONENTS
    assert manifest["last_round"]["new_module_count"] == len(registration["new_modules"]) == 4
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
    assert scan["scanned_module_count"] == 861 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 4210 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 17, "new_selected_declarations": 20,
        "all_source_modules_scanned": 861, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 4210,
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
