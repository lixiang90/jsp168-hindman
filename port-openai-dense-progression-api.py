from pathlib import Path
import hashlib,json,time,re,sys

root=Path('dependencies/openai-dense-progressions')
rules={
 'Mathlib.Basic.NNReal.Defs':'Mathlib.Data.NNReal.Defs',
 'Mathlib.Basic.Real.Basic':'Mathlib.Data.Real.Basic',
 'Set.mem_ofPred_eq':'Set.mem_setOf_eq',
 'mem_ofPred_eq':'Set.mem_setOf_eq',
 'dite_eq_left':'dif_pos', 'dite_eq_right':'dif_neg',
 'ite_eq_left':'if_pos', 'ite_eq_right':'if_neg',
 'TensorProduct.inductionOn':'TensorProduct.induction_on',
 'Finset.prod_le_prod':"Finset.prod_le_prod'",
 'Finset.prod_le_one':"Finset.prod_le_one'",
 'Finset.one_le_prod':"Finset.one_le_prod'",
 'Finset.prod_le_prod_of_subset_of_one_le':"Finset.prod_le_prod_of_subset_of_one_le'",
 'Finset.prod_le_prod_of_subset_of_le_one':"Finset.prod_le_prod_of_subset_of_le_one'",
 'Finset.prod_le_prod₀':'Finset.prod_le_prod',
 'Finset.prod_le_one₀':'Finset.prod_le_one',
 'Finset.one_le_prod₀':'Finset.one_le_prod',
 'Finset.prod_le_prod_of_subset_of_one_le₀':'Finset.prod_le_prod_of_subset_of_one_le',
 'Finset.prod_le_prod_of_subset_of_le_one₀':'Finset.prod_le_prod_of_subset_of_le_one',
 'OrderEmbedding.range_inj_of_wellFoundedLT':'OrderEmbedding.range_inj',
 'Matrix.det_of_isUpperTriangular':'Matrix.det_of_upperTriangular',
 'Matrix.det_of_isLowerTriangular':'Matrix.det_of_lowerTriangular',
 'Measurable.of_eval':'measurable_pi_iff.mpr',
 'Complex.isometry_ofReal.lipschitzWith':'Complex.isometry_ofReal.lipschitz',
 'lipschitzWith':'lipschitz',
 'Mathlib.Basic.Complex.Basic':'Mathlib.Data.Complex.Basic',
 'Mathlib.Basic.NNReal.Basic':'Mathlib.Data.NNReal.Basic',
 'Mathlib.Analysis.Normed.Module.Seminorm.Basic':'Mathlib.Analysis.Seminorm',
 'Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible':'Mathlib.Topology.Algebra.Module.Equiv',
 'Mathlib.Analysis.InnerProductSpace.ExteriorPower':'OAI.Compatibility.MathlibExteriorPower',
}
record=[]
original=json.loads((root/'SOURCE-MANIFEST.json').read_text(encoding='utf-8'))
items=original['files']
scope='entire isolated source archive'
if '--finite-only' in sys.argv:
 selected=set(json.loads(Path('openai-finite-szemeredi-selected-closure.json').read_text(encoding='utf-8'))['modules'])
 items=[item for item in items if item['module'] in selected]
 assert len(items)==len(selected)
 scope='actual finite Szemeredi and off-diagonal extraction closure'
for item in items:
 path=root/item['path']
 raw=path.read_bytes()
 origin=Path(item.get('immutable_original_path',str(Path('E:/codex-build/math/lean')/item['path']))).read_bytes()
 assert hashlib.sha256(origin).hexdigest()==item['original_sha256']
 source=origin.decode('utf-8-sig').replace('\r\n','\n')
 changes={}
 for old,new in rules.items():
  source,count=re.subn(r"(?<![\w'])"+re.escape(old)+r"(?![\w'])",new,source)
  if count: changes[old]=count
 for old,new in [('.IsLowerTriangular','.BlockTriangular OrderDual.toDual'),
                 ('.IsUpperTriangular','.BlockTriangular id')]:
  source,count=re.subn(re.escape(old)+r"(?![\w'])",new,source)
  if count: changes[old]=dict(replacement=new,count=count)
 if item['module']=='OAI.Combinatorics.Progressions.Model':
  source=source.replace('import Mathlib\n',
    'import Mathlib.Analysis.SpecialFunctions.Pow.Real\nimport Mathlib.Data.Finset.Powerset\nimport Mathlib.Topology.Algebra.InfiniteSum.Real\n',1)
  changes['whole Mathlib import']='minimal definition imports; all original definitions and quantifiers unchanged'
 if item['module'].endswith('.SourceFullCoarseTargetRegularity'):
  source=source.replace('            convert htopGap using 1',
    '            convert htopGap using 1 <;> rfl')
  source=source.replace('''              (next chosen).reciprocal_gap_le lower q using 1
            · congr 1''', '''              (next chosen).reciprocal_gap_le lower q using 1
            · congr 1
            · rfl''')
  changes['reciprocal gap convert closure']='close actual remaining reflexive equalities explicitly for Lean 4.32.2'
 if item['module'].endswith('.BooleanCubeModeWitness'):
  source=source.replace('AddMonoidAlgebra.coeff_add','MvPolynomial.coeff_add')
  changes['AddMonoidAlgebra.coeff_add']='MvPolynomial.coeff_add'
 if item['module'].endswith('.BufferedSiteExpansion'):
  source=source.replace('dist_star_star','Complex.star_def, Complex.dist_conj_conj')
  changes['dist_star_star']='Complex.star_def and Complex.dist_conj_conj (complex-valued functions only)'
 if item['module'].endswith('.CappedDistanceReconstruction'):
  source=source.replace('Complex.isometry_ofReal.lipschitzWith.comp','Complex.isometry_ofReal.lipschitz.comp')
  changes['Complex.isometry_ofReal.lipschitzWith']='Complex.isometry_ofReal.lipschitz'
 if item['module'].endswith('.FrozenCosetVariation'):
  source=source.replace('.lipschitzWith', '.lipschitz')
  changes['isometry multiplication Lipschitz API']='Isometry.lipschitz for the three actual right-multiplication isometries'
 if item['module'].endswith('.LatticeMeasurableRepresentative'):
  source=source.replace('.domRestrict', '.restrict')
  source=source.replace('hcont.continuousOn.measurableEmbedding (ZSpan.fundamentalDomain_measurableSet b) hinj',
    'ContinuousOn.measurableEmbedding (ZSpan.fundamentalDomain_measurableSet b) hcont.continuousOn hinj')
  changes['fundamental-domain measurable restriction']='old Set.restrict and explicit measurable-set-first embedding signature'
 if item['module'].endswith('.LatticeHyperplaneBasis'):
  source=source.replace('''@AddSubgroup.isClosed_of_discreteTopology E _ _ _ _
    Λ.toAddSubgroup (inferInstanceAs (DiscreteTopology Λ))''',
    'AddSubgroup.isClosed_of_discrete (H := Λ.toAddSubgroup)')
  changes['closed discrete lattice']='old isClosed_of_discrete with actual lattice subgroup'
 if item['module'].endswith('.BaseChangeCoordinateProjection'):
  source=source.replace('  induction x using TensorProduct.induction_on with\n',
    '  induction x using TensorProduct.induction_on with\n  | zero => simp\n')
  changes['tensor base-change coordinate induction']='two explicit old zero cases proved by linearity'
 if item['module'].endswith('.BasisGradedCoordinateBasis'):
  source=source.replace('  simpa only [basisBelowProjection, Set.compl_ofPred, not_lt] using',
    '''  have hcompl : {i | w i < j}ᶜ = {i | j ≤ w i} := by
    ext i
    simp
  simpa only [basisBelowProjection, hcompl] using''')
  changes['set predicate complement']='actual complement equality proved pointwise'
 if item['module'].endswith('.OrderedBoundaryPartition'):
  source=source.replace('        simp [eraseCoordinate_eq_removeNth]',
    '        simp [eraseCoordinate_eq_removeNth] <;> rfl')
  changes['deletion cylinder extensional equality']='close residual identical membership equivalence by reflexivity'
 if item['module'].endswith(('.StrongOrderedComplexRegularity','.CoarseTargetRegularity',
                             '.AdaptiveCoarseTargetRegularity')):
  source=re.sub(r'convert (hgap|hcomplexity) using 1(?:; rfl)?(?!\s*<;>)',
    r'convert \1 using 1 <;> rfl', source)
  source=re.sub(r'(convert (?:hgap|hcomplexity) using 1 <;> rfl)\n[ \t]+rfl(?=\n)',
    r'\1',source)
  changes['recursive regularity certificate conversion']='close all old convert-generated definitional equality goals by reflexivity'
 if item['module'].endswith('.TowerDominatingGrowth'):
  source=source.replace('convert h using 1', 'convert h using 1 <;> rfl')
  changes['growth certificate conversion']='close old convert-generated identical complexity equalities by reflexivity'
 if item['module'].endswith('.FreePrimitiveCriterion'):
  source=source.replace('| of_mul x w _ => simp', '| mul_of w x _ => simp')
  changes['free monoid word induction']='old right-generator induction case; augmentation vanishes by the same simp proof'
 if item['module'].endswith('.ResidueRefinedPeriod'):
  helper_path=Path('check-matrix-injectivity.lean')
  helper_source=helper_path.read_text(encoding='utf-8')
  helper='namespace Matrix\n'+helper_source.split('namespace Matrix\n',1)[1]
  source=source.replace('namespace OAI\n', helper+'\nnamespace OAI\n',1)
  changes['nonsingular matrix injectivity']=dict(proved_helper_source=helper_path.as_posix(),
    sha256=hashlib.sha256(helper_path.read_bytes()).hexdigest(),
    construction='actual subtraction, old mulVec zero-kernel theorem, sub_eq_zero')
 if item['module'].endswith('.IntegerFiberUniformBound'):
  source='import OAI.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod\n'+source
  changes['nonsingular matrix helper import']='genuinely proved helper from the existing Mathlib-only residue module'
 if item['module'].endswith('.FiniteGradedBranchPrefixLog'):
  source=source.replace('Finset.prod_le_prod (fun j hj',"Finset.prod_le_prod' (fun j hj")
  changes['natural-product comparison']='Finset.prod_le_prod prime'
 if item['module'].endswith('.RationalHeight'):
  source=source.replace('Finset.prod_le_prod fun', "Finset.prod_le_prod' fun")
  changes['natural rational denominator product bounds']='Finset.prod_le_prod prime'
 if item['module'].endswith('.CharacterCoordinateScale'):
  source=source.replace('Finset.prod_le_prod (fun', "Finset.prod_le_prod' (fun")
  changes['natural character order product bounds']='Finset.prod_le_prod prime'
 if item['module'].endswith('.ExponentialBohrVolume'):
  source=source.replace('''  congr 1
  ring_nf
  rfl''','''  congr 1
  ring_nf''')
  changes['character_comm proof']='old ring_nf closes the equality; remove redundant rfl'
 if item['module'].endswith('.NormalizedRestrictionTransport'):
  source=source.replace('Measure.map_smul _ e.measurable.aemeasurable', 'Measure.map_smul')
  changes['measure scalar transport']='old unconditional map_smul signature'
 if item['module'].endswith('.AllocatedUniformGridVolumeCap'):
  helper_path=Path('check-positive-prod-injection.lean')
  helper_source=helper_path.read_text(encoding='utf-8')
  helper=helper_source.split('namespace OAI\n',1)[1].rsplit('end OAI',1)[0]
  source=source.replace('namespace OAI\n', 'namespace OAI\nopen scoped BigOperators\n'+helper,1)
  source=source.replace('Finset.prod_le_prod_of_injOn₀','OAI.real_prod_le_prod_of_injective')
  changes['nonnegative injection product comparison']=dict(
   proved_helper_source=helper_path.as_posix(),sha256=hashlib.sha256(helper_path.read_bytes()).hexdigest(),
   construction='old nonnegative pointwise comparison, true product_image, exact image subset comparison')
 if item['module'].endswith('.RealSubquotientEquiv'):
  source=source.replace('''  induction x using TensorProduct.induction_on with
  | tmul r x => rfl''','''  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | tmul r x => rfl''')
  changes['tensor product induction']='explicit old zero case, proved by map_zero'
 if item['module'].endswith('.TensorContraction'):
  source=source.replace('  induction t using TensorProduct.induction_on with\n',
                        '  induction t using TensorProduct.induction_on with\n  | zero => simp\n')
  changes['tensor contraction induction']='explicit old zero cases, proved by zero multiplication and map_zero'
 if item['module'].endswith('.FiniteInversePerturbation'):
  source=source.replace('Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible','Mathlib.Topology.Algebra.Module.Equiv')
  changes['invertible continuous linear map import']='existing Equiv module'
 if item['module'].endswith('.LowerTriangularMinor'):
  source=source.replace('B.IsLowerTriangular', 'B.BlockTriangular OrderDual.toDual')
  source=source.replace('Matrix.det_of_isLowerTriangular B hB', 'Matrix.det_of_lowerTriangular B hB')
  changes['lower triangular determinant']='existing BlockTriangular OrderDual API'
 if item['module'].endswith('.FreimanInverseLift'):
  source=source.replace('''      simp only [ruzsaModelMap, ruzsaRepresentativeSum, Multiset.map_cons,
        Multiset.sum_cons, Nat.cast_add, ih]''','''      rw [Multiset.map_cons, Multiset.sum_cons]
      rw [show ruzsaRepresentativeSum q lam (a ::ₘ T) =
        ruzsaRepresentative q lam a + ruzsaRepresentativeSum q lam T by
          simp [ruzsaRepresentativeSum]]
      rw [Nat.cast_add, ih]
      rfl''')
  changes['ruzsaModelMap_sum proof']='retain recursive map in induction hypothesis'
 if item['module'].endswith('.FormalExpLog'):
  source=re.sub(r'\bderivative(?![A-Za-z0-9_])', 'derivative ℚ', source)
  source=source.replace('derivative_log','deriv_log')
  source=source.replace('derivative_subst HasSubst.exp_sub_one','derivative_subst ℚ HasSubst.exp_sub_one')
  source=source.replace('''  apply subst_eq_X_of_subst_eq_X (log ℚ) constantCoeff_log
    (by rw [coeff_one_log]; exact isUnit_one) HasSubst.exp_sub_one
  exact formal_log_exp''','''  have hu : IsUnit (coeff 1 (log ℚ)) := by
    rw [coeff_one_log]
    exact isUnit_one
  let r : PowerSeries ℚ := (log ℚ).substInvOfIsUnit hu
  have hr : r.subst (log ℚ) = X :=
    subst_substInvOfIsUnit_left (log ℚ) constantCoeff_log hu
  have hq : exp ℚ - 1 = r := by
    calc
      (exp ℚ - 1 : PowerSeries ℚ) =
          PowerSeries.subst (exp ℚ - 1) (PowerSeries.subst (log ℚ) r) := by
        rw [hr, subst_X HasSubst.exp_sub_one]
      _ = PowerSeries.subst (PowerSeries.subst (exp ℚ - 1) (log ℚ)) r := by
        rw [subst_comp_subst_apply HasSubst.log HasSubst.exp_sub_one]
      _ = r := by rw [formal_log_exp, X_subst]
  rw [hq]
  exact hr''')
  changes['formal exp/log proof']='explicit rational derivative and existing two-sided substitution inverse'
 if item['module']=='OAI.Compatibility.MathlibExteriorPower':
  source=source.replace('namespace exteriorPower\n', '''namespace Matrix

theorem gram_eq_one_iff_orthonormal {ι E : Type*} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {v : ι → E} :
    gram ℝ v = 1 ↔ Orthonormal ℝ v := by
  rw [orthonormal_iff_ite]
  constructor
  · intro h i j
    simpa only [gram_apply, Matrix.one_apply] using congrArg (fun M => M i j) h
  · intro h
    ext i j
    simpa only [gram_apply, Matrix.one_apply] using h i j

end Matrix

namespace exteriorPower
''',1)
  changes['missing orthonormal Gram equivalence']='entrywise proof from old orthonormal_iff_ite'
 if source.encode('utf-8')==raw: continue
 path.write_bytes(source.encode('utf-8'))
 record.append(dict(path=path.relative_to(root).as_posix(),before_sha256=hashlib.sha256(raw).hexdigest(),
                    after_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),replacements=changes))
log=root/'API-COMPATIBILITY-EDITS.json'
prior=json.loads(log.read_text(encoding='utf-8')) if log.exists() else []
prior.append(dict(timestamp=time.time(),scope=scope,rules=rules,files=record,
 semantic_intent='API and proof compatibility; preserve original mathematical statements and assumptions without compiler-option changes. Additional attributed helpers require genuine proofs. Every edited module still needs actual Lean verification.'))
log.write_text(json.dumps(prior,indent=2),encoding='utf-8')
original.update(proof_sources_unmodified=False,api_compatibility_edits='API-COMPATIBILITY-EDITS.json',
                classification='ISOLATED PORT CANDIDATE; not a verified/registered project dependency')
(root/'SOURCE-MANIFEST.json').write_text(json.dumps(original,indent=2),encoding='utf-8')
config=root/'lakefile.toml'
text=config.read_text(encoding='utf-8')
if 'packagesDir =' not in text:
 text=text.replace('version = "0.1.0"','version = "0.1.0"\npackagesDir = "'+(Path.cwd()/'.lake/packages').as_posix()+'"')
 config.write_text(text,encoding='utf-8')
print(json.dumps(dict(edited_files=len(record),project_registered_sources_changed=False,candidate_verified=False)))
