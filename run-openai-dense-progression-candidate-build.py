from pathlib import Path
import hashlib, json, subprocess, time

root=Path('dependencies/openai-dense-progressions')
log=Path('openai-dense-progression-candidate-build.txt')
start=time.monotonic()
command=['lake','build','OAI.Combinatorics.Progressions.Results.Conclusions']
with log.open('wb') as stream:
 result=subprocess.run(command,cwd=root,stdout=stream,stderr=subprocess.STDOUT)
record=dict(command=command,working_directory=root.resolve().as_posix(),terminal=True,
            exit_code=result.returncode,elapsed_seconds=time.monotonic()-start,
            log=log.as_posix(),log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
            current_main_project_proof_dependency=False)
Path('openai-dense-progression-candidate-build-result.json').write_text(json.dumps(record,indent=2),encoding='utf-8')
print(json.dumps(record))
raise SystemExit(result.returncode)
