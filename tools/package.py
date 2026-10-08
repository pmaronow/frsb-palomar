#!/usr/bin/env python3
"""Copy the clean repository and create a deterministic distributable ZIP.

Reports and raw logs stay outside the archive. Packaging incomplete verification
requires --allow-unverified and records each gap in the companion manifest.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import zipfile

from source_inventory import candidate_files, source_snapshot, snapshot_digest


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--name", default="frsb-palomar")
    parser.add_argument("--audit-report", type=Path, default=Path("../verification/audit-report.json"))
    parser.add_argument("--build-report", type=Path, default=Path("../verification/build-all.json"))
    parser.add_argument("--preflight-report", type=Path, default=Path("../verification/submission-preflight.json"))
    parser.add_argument("--comparator-report", type=Path, default=Path("../verification/comparator.json"))
    parser.add_argument("--allow-unverified", action="store_true")
    args = parser.parse_args()
    if not args.name.replace("-", "").replace("_", "").isalnum():
        raise SystemExit("Repository name must contain only letters, numbers, hyphens and underscores")
    root = Path(__file__).resolve().parents[1]
    output = args.output.resolve()
    if output.is_relative_to(root):
        raise SystemExit("Deliverables must be outside the source repository")
    output.mkdir(parents=True, exist_ok=True)
    snapshot = source_snapshot(root)
    packaged = {path.relative_to(root).as_posix(): path for path in candidate_files(root)}
    checks = {}
    blockers = []
    for label, supplied in (("audit", args.audit_report), ("all_sources_build", args.build_report),
                            ("structural_metadata_preflight", args.preflight_report), ("comparator_kernels", args.comparator_report)):
        path = (root / supplied).resolve()
        if not path.is_file():
            checks[label] = {"status": "not_run"}
            blockers.append(f"{label}: report missing")
            continue
        report = json.loads(path.read_text(encoding="utf-8"))
        current = report.get("source_sha256") == snapshot
        checks[label] = {"status": report.get("status", "unknown"), "source_current": current,
                         "report_sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
        if report.get("status") != "passed" or not current:
            blockers.append(f"{label}: {report.get('status', 'unknown')}; source current={current}")
        if label == "audit" and report.get("coverage", {}).get("status") != "passed":
            blockers.append("coverage: external source-ledger check did not pass")
    if blockers and not args.allow_unverified:
        raise SystemExit("Verification is incomplete; use --allow-unverified to deliver clearly labelled source. " + "; ".join(blockers))
    destination = output / args.name
    if destination.exists():
        raise SystemExit(f"Refusing to overwrite existing repository: {destination}")
    with tempfile.TemporaryDirectory(prefix="frsb-package-", dir=output) as scratch:
        staged = Path(scratch) / args.name
        for name, source in packaged.items():
            target = staged / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)
        if source_snapshot(staged) != snapshot or source_snapshot(root) != snapshot:
            raise SystemExit("Sources changed while packaging")
        archive = output / f"{args.name}-source.zip"
        temporary_archive = Path(scratch) / "source.zip"
        with zipfile.ZipFile(temporary_archive, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as handle:
            for name in sorted(packaged):
                info = zipfile.ZipInfo(args.name + "/" + name, date_time=(2026, 1, 1, 0, 0, 0))
                mode = 0o755 if (root / name).stat().st_mode & 0o111 else 0o644
                info.external_attr = (0o100000 | mode) << 16
                info.compress_type = zipfile.ZIP_DEFLATED
                handle.writestr(info, (root / name).read_bytes())
        staged.replace(destination)
        temporary_archive.replace(archive)
    manifest = {"repository": args.name, "archive": archive.name,
                "archive_sha256": hashlib.sha256(archive.read_bytes()).hexdigest(),
                "source_snapshot_sha256": snapshot_digest(snapshot), "source_sha256": snapshot,
                "verification_complete": not blockers, "checks": checks, "blockers": blockers,
                "note": "Local preparation evidence; publication, Palomar submission, registration and approval have not occurred"}
    manifest_path = output / f"{args.name}-verification.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    (output / f"{args.name}-SHA256SUMS").write_text("".join(
        hashlib.sha256(path.read_bytes()).hexdigest() + "  " + path.name + "\n" for path in (archive, manifest_path)), encoding="utf-8")
    print(json.dumps({"repository": str(destination), "archive": str(archive), "source_file_count": len(snapshot),
                      "verification_complete": not blockers, "blockers": blockers}))


if __name__ == "__main__":
    main()
