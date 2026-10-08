#!/usr/bin/env python3
"""Run protected local Comparator configuration and record all three kernels."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

from source_inventory import revision, source_snapshot, snapshot_digest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, default=Path("../verification/comparator.json"))
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    path = (root / args.report).resolve()
    path.parent.mkdir(parents=True, exist_ok=True)
    snapshot = source_snapshot(root)
    report = {"check": "local_comparator_and_independent_kernels", "status": "not_run",
              "started_at": datetime.now(timezone.utc).isoformat(), "source_sha256": snapshot,
              "source_snapshot_sha256": snapshot_digest(snapshot), "source_revision": revision(root),
              "required_kernels": ["Lean", "nanoda", "con-ron"]}
    tools = {}
    lean = shutil.which("lean")
    if lean:
        prefix_result = subprocess.run([lean, "--print-prefix"], cwd=root, capture_output=True, text=True)
        prefix = Path(prefix_result.stdout.strip()) if prefix_result.returncode == 0 else None
        if prefix:
            for name in ("lean", "lake", "leanexport", "leanchecker", "nanoda_bin", "con-ron"):
                binary = prefix / "bin" / name
                tools[name] = {"path": str(binary), "sha256": hashlib.sha256(binary.read_bytes()).hexdigest() if binary.is_file() else None}
    report["toolchain_executables"] = tools
    result = subprocess.run(["bash", "tools/verify_comparator.sh"], cwd=root, capture_output=True, text=True)
    output = result.stdout + result.stderr
    path.with_suffix(".log").write_text(output, encoding="utf-8")
    report["return_code"] = result.returncode
    markers = {"Lean": "Lean default kernel accepts the solution",
               "nanoda": "nanoda kernel accepts the solution",
               "con-ron": "con-ron kernel accepts the solution"}
    report["kernel_verdicts"] = {name: "passed" if marker in output else "failed_or_missing"
                                 for name, marker in markers.items()}
    report["comparator_acceptance_marker"] = "Your solution is okay!" in output
    passed = result.returncode == 0 and all(status == "passed" for status in report["kernel_verdicts"].values()) and report["comparator_acceptance_marker"]
    report["source_changed_during_check"] = snapshot != source_snapshot(root)
    report["status"] = "passed" if passed and not report["source_changed_during_check"] else "failed"
    if report["status"] != "passed":
        report["failure_excerpt"] = output[-5000:]
    report["finished_at"] = datetime.now(timezone.utc).isoformat()
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in ("status", "return_code", "kernel_verdicts", "source_snapshot_sha256")}))
    print(f"Report: {path}")
    return int(report["status"] != "passed")


if __name__ == "__main__":
    sys.exit(main())
