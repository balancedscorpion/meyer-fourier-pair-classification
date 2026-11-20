"""Report and check transitive axioms for every configured Solution declaration."""
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
for entry in ("WholeSpace", "LowerRay"):
    config = json.loads((ROOT / entry / "comparator.json").read_text())
    names = config["theorem_names"] + config["definition_names"]
    allowed = set(config["permitted_axioms"])
    subprocess.run(["lake", "build", config["solution_module"]], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory() as folder:
        probe = Path(folder) / "Audit.lean"
        probe.write_text("module\nimport " + config["solution_module"] + "\n"
                         + "".join(f"#print axioms {name}\n" for name in names))
        result = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT,
                                check=True, stdout=subprocess.PIPE, text=True)
    for name in names:
        match = re.search("'" + re.escape(name) + r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", result.stdout)
        if match is None:
            raise SystemExit(f"Missing axiom report for {name}")
        actual = {a.strip() for a in (match[1] or "").split(",") if a.strip()}
        print(f"{entry}/{name}: {', '.join(sorted(actual)) or 'none'}", flush=True)
        if extra := actual - allowed:
            raise SystemExit(f"Unexpected axioms in {name}: {sorted(extra)}")
