from pathlib import Path
import hashlib
import json
import subprocess
import sys
import time

prefix = "round-group-lie-nilpotency"
sys.stdout.reconfigure(encoding="utf-8")
assert sys.argv[1] in {"build", "kernel"}
suffix = sys.argv[1]
if suffix == "kernel":
    checked = json.loads(Path(prefix + "-build-result.json").read_text(encoding="utf-8"))
    assert checked["terminal"] and checked["exit_code"] == 0
    assert checked["log_sha256"] == hashlib.sha256(Path(prefix + "-build.txt").read_bytes()).hexdigest()
command = ["lake", "build"] if suffix == "build" else ["lake", "env", "lean", "Verification.lean"]
log = Path(prefix + ("-build.txt" if suffix == "build" else "-axioms.txt"))
start = time.monotonic()
with log.open("wb") as stream:
    result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
record = {"command": command, "exit_code": result.returncode, "terminal": True,
          "elapsed_seconds": time.monotonic() - start,
          "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest()}
Path(prefix + "-" + suffix + "-result.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
print(json.dumps(record))
if result.returncode:
    print(log.read_text(encoding="utf-8")[-14000:])
sys.exit(result.returncode)
