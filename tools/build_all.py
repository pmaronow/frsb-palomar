#!/usr/bin/env python3
"""Build every submitted Lean module, including unused vendored modules.

Requires Python 3.11+ and a TOML Lake project. Evidence defaults to ../verification
and is excluded from the public repository. This does not authenticate upstream
dependencies or replace Palomar's trusted build.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tomllib

from source_inventory import candidate_files, revision, source_snapshot, snapshot_digest


def modules(root: Path) -> list[str]:
    settings = tomllib.loads((root / "lakefile.toml").read_text())
    directories = [root]
    directories += [(root / library["srcDir"]).resolve() for library in settings.get("lean_lib", [])
                    if isinstance(library, dict) and isinstance(library.get("srcDir"), str)]
    directories = sorted(set(directories), key=lambda path: len(path.parts), reverse=True)
    names = []
    for path in candidate_files(root):
        if path.suffix != ".lean" or path.name == "lakefile.lean":
            continue
        directory = next((directory for directory in directories if path.is_relative_to(directory)), None)
        if directory is None:
            raise ValueError(f"No Lake source directory covers {path.relative_to(root)}")
        name = ".".join(path.relative_to(directory).with_suffix("").parts)
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", name):
            raise ValueError(f"Unsupported module path: {path.relative_to(root)}")
        names.append(name)
    if len(names) != len(set(names)):
        raise ValueError("Duplicate module names across source directories")
    return sorted(names)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--report", type=Path, default=Path("../verification/build-all.json"))
    parser.add_argument("--list-only", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    names = modules(root)
    if args.list_only:
        print("\n".join(names))
        return 0
    snapshot = source_snapshot(root)
    path = (root / args.report).resolve()
    path.parent.mkdir(parents=True, exist_ok=True)
    logfile = path.with_suffix(".log")
    lake = shutil.which(args.lake)
    report = {"check": "all_submitted_lean_modules", "status": "not_run",
              "started_at": datetime.now(timezone.utc).isoformat(), "modules": names,
              "module_count": len(names), "source_sha256": snapshot,
              "source_snapshot_sha256": snapshot_digest(snapshot), "source_revision": revision(root)}
    if lake is None:
        report.update(status="failed", error="Lake executable not found")
        result_code = 1
    else:
        argv = [lake, "build", *["+" + name + ":olean" for name in names]]
        report["command"] = [args.lake, *argv[1:]]
        with logfile.open("w", encoding="utf-8") as handle:
            result = subprocess.run(argv, cwd=root, stdout=handle, stderr=subprocess.STDOUT, text=True)
        report.update(status="passed" if result.returncode == 0 else "failed", return_code=result.returncode)
        result_code = int(result.returncode != 0)
    report["source_changed_during_build"] = snapshot != source_snapshot(root)
    if report["source_changed_during_build"]:
        report["status"] = "source_changed_during_build"
        result_code = 1
    report["finished_at"] = datetime.now(timezone.utc).isoformat()
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report.get(key) for key in ("status", "module_count", "return_code", "source_changed_during_build")}))
    print(f"Report: {path}")
    return result_code


if __name__ == "__main__":
    sys.exit(main())
