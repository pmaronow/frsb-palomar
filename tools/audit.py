#!/usr/bin/env python3
"""Audit project declarations without treating proposition definitions as proofs.

Run after installing the pinned Lean toolchain and Mathlib cache:
    python3 tools/audit.py --paper-source ../paper-source/main.tex
Generated Lean, logs, and JSON reports default to ../verification, outside the
public repository. Imported constants from every original module are audited,
including generated declarations and instances, rather than just theorem names.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

from source_inventory import source_snapshot, snapshot_digest, revision

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(?:sorry|admit|sorryAx|axiom|constant|native_decide)\b")
VENDOR_FORBIDDEN = re.compile(r"\b(?:sorry|admit|sorryAx|axiom|native_decide)\b")
NUMBERED_RESULT_IDS = tuple(
    f"{section}_{number}"
    for section, count in ((1, 2), (2, 7), (3, 4), (4, 3), (5, 6), (6, 4))
    for number in range(1, count + 1)
)
NUMBERED_TARGET_PROOFS = {
    f"FRSB.Numbered.Statement_{number}": f"FRSB.Numbered.result_{number}"
    for number in NUMBERED_RESULT_IDS
}
# The original foundation remains independently checked in this project.
FOUNDATION_NUMBERS = ("1_1", "1_2", "2_1", "2_2", "2_3", "3_1", "4_1", "5_1", "5_2", "5_3", "5_4", "5_5", "5_6", "6_1", "6_2")
TARGET_PROOFS = {
    "FRSB.FullRSBTarget": "FRSB.fullRSB",
    "FRSB.QuantitativeAtomTarget": "FRSB.quantitative_atom",
    "FRSB.FiniteAtomicApproximationTarget": "FRSB.finite_atomic_approximation",
    "FRSB.PDERegularityTarget": "FRSB.pde_regularity",
    "Paper.MainReplicaSymmetryTarget": "Paper.replicaSymmetry",
    "Paper.SmoothATBoundaryTarget": "Paper.smoothATBoundary",
    "Paper.StrictReplicaSymmetryTarget": "Paper.strictReplicaSymmetry",
    **{f"Paper.Numbered.Statement_{n}": f"Paper.Numbered.result_{n}" for n in FOUNDATION_NUMBERS},
    **NUMBERED_TARGET_PROOFS,
}
TARGET_TYPES = {
    "FRSB.PDERegularityTarget": "∀ β : ℝ, FRSB.PDERegularityTarget β",
}


def scan_challenge(root: Path, selected: list[str]) -> dict:
    """Permit only selected theorem holes, each with the exact body `by sorry`."""
    path = root / "Challenge.lean"
    if not path.is_file():
        return {"status": "failed", "errors": ["Challenge.lean is missing"], "intentional_holes": []}
    masked = mask_comments_and_strings(path.read_text(encoding="utf-8"))
    allowed_offsets = set()
    holes = []
    for match in re.finditer(
        r"(?m)^\s*(?:public\s+)?(?:theorem|lemma)\s+(?P<name>[\w'.]+)\b"
        r"(?:(?!^\s*(?:theorem|lemma|def|abbrev|opaque|end)\b)[\s\S])*?"
        r":=\s*by\s+(?P<hole>sorry)\b"
        r"(?=\s*(?:\Z|(?:public\s+)?\b(?:end|theorem|lemma|def|abbrev|opaque)\b))", masked):
        short = match.group("name")
        candidates = [name for name in selected if name == short or name.rsplit(".", 1)[-1] == short]
        if len(candidates) == 1:
            allowed_offsets.add(match.start("hole"))
            holes.append({"declaration": candidates[0],
                          "line": masked.count("\n", 0, match.start("hole")) + 1})
    errors = []
    for match in FORBIDDEN.finditer(masked):
        if match.group() == "sorry" and match.start() in allowed_offsets:
            continue
        errors.append({"file": "Challenge.lean", "line": masked.count("\n", 0, match.start()) + 1,
                       "token": match.group()})
    if {hole["declaration"] for hole in holes} != set(selected) or len(holes) != len(selected):
        errors.append("Each selected Challenge theorem must have exactly one intentional `by sorry` body")
    return {"status": "failed" if errors else "passed", "errors": errors, "intentional_holes": holes}


def environment_audit_source() -> str:
    # Public module imports never include Challenge: its selected theorem names
    # intentionally coincide with Solution and its holes are not dependencies.
    return '''module
public import FRSB
public import Paper
public import Solution
public import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants do
    if let some index := env.getModuleIdxFor? name then
      let origin := env.allImportedModuleNames[index.toNat]!
      let moduleName := origin.toString
      if moduleName == "FRSB" || moduleName.startsWith "FRSB." ||
          moduleName == "Paper" || moduleName.startsWith "Paper." || moduleName == "Solution" then
        let axioms ← Lean.collectAxioms name
        let row := Json.mkObj [
          ("name", toJson name.toString), ("module", toJson moduleName),
          ("axioms", toJson (axioms.toList.map Name.toString))]
        logInfo m!"AUDIT_CONSTANT {row.compress}"
'''


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scan-only", action="store_true", help="Scan sources; Lean/build statuses remain not_run")
    parser.add_argument("--no-build", action="store_true", help="Use already-built modules; build status remains skipped_by_request")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--paper-source", type=Path, help="External manuscript source matching the coverage ledger")
    parser.add_argument("--skip-coverage", action="store_true", help="Run formal proof checks only; records coverage as not_run and cannot support complete packaging")
    parser.add_argument("--report", type=Path, default=Path("../verification/audit-report.json"))
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    report_path = (root / args.report).resolve()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    work = report_path.parent
    paper = (root / args.paper_source).resolve() if args.paper_source else None
    snapshot = source_snapshot(root)
    declarations, violations = scan_sources(root)
    vendor_count, vendor_violations = scan_vendor_sources(root)
    config = json.loads((root / "comparator.json").read_text()) if (root / "comparator.json").is_file() else {}
    selected = config.get("theorem_names", [])
    challenge = scan_challenge(root, selected)
    report = {
        "schema_version": 5, "started_at": datetime.now(timezone.utc).isoformat(),
        "source_sha256": snapshot, "source_snapshot_sha256": snapshot_digest(snapshot),
        "source_revision": revision(root), "standard_axiom_whitelist": sorted(STANDARD_AXIOMS),
        "source_scan": "passed" if not violations else "failed", "source_violations": violations,
        "challenge_scan": challenge, "vendor_source_scan": "passed" if not vendor_violations else "failed",
        "vendor_source_file_count": vendor_count, "vendor_source_violations": vendor_violations,
        "build_status": "not_run", "lean_audit_status": "not_run",
        "aggregate_modules": ["FRSB", "Paper", "Solution"],
        "numbered_results": [{"number": n.replace("_", "."), "target": target, "proof": proof,
                             "closed_proof_check": "not_run"}
                            for n, (target, proof) in zip(NUMBERED_RESULT_IDS, NUMBERED_TARGET_PROOFS.items())],
        "foundation_numbered_results": [{"number": n.replace("_", "."),
            "target": f"Paper.Numbered.Statement_{n}", "proof": f"Paper.Numbered.result_{n}",
            "closed_proof_check": "not_run"} for n in FOUNDATION_NUMBERS],
        "selected_solution_proofs": [{"declaration": name, "axiom_check": "not_run"} for name in selected],
        "declarations": declarations,
        "classification_note": "A Prop-valued definition describes a proposition; its designated typed proof must check. "
            "All imported original-module constants (including instances and generated declarations) are axiom-audited. "
            "Explicit hypotheses remain mathematical assumptions. Challenge theorem holes are audited separately and never imported into proofs. "
            "This checks formal typing and axioms, not semantic correspondence to the paper or human mathematical review.",
    }
    errors = bool(violations or vendor_violations or challenge["errors"] or not selected)
    public = [d for d in declarations if not d["private"]]
    report["unassigned_targets"] = [d["name"] for d in public if d["classification"] == "target_definition" and d["name"] not in TARGET_PROOFS]
    errors |= bool(report["unassigned_targets"])
    if not args.scan_only:
        lake = shutil.which(args.lake)
        if lake is None:
            report.update(lean_audit_status="failed", error="Lake executable not found")
            errors = True
        else:
            build_ok = True
            if args.no_build:
                report["build_status"] = "skipped_by_request"
            else:
                build = run_command([lake, "build", "FRSB", "Paper", "Challenge", "Solution"], root, work / "audit-build.log")
                build_ok = build.returncode == 0
                report.update(build_status="passed" if build_ok else "failed", build_return_code=build.returncode)
                errors |= not build_ok
            if build_ok:
                scratch = work / "Audit.lean"
                scratch.write_text(environment_audit_source() + "\n" + "".join(
                    f"example : {TARGET_TYPES.get(target, target)} := {proof}\n" for target, proof in TARGET_PROOFS.items()), encoding="utf-8")
                lean = run_command([lake, "env", "lean", str(scratch)], root, work / "audit-lean.log")
                report["lean_return_code"] = lean.returncode
                dependencies = {}
                constants = []
                for line in (lean.stdout + lean.stderr).splitlines():
                    if "AUDIT_CONSTANT " in line:
                        row = json.loads(line.split("AUDIT_CONSTANT ", 1)[1])
                        row["unexpected_axioms"] = sorted(set(row["axioms"]) - STANDARD_AXIOMS)
                        row["axiom_check"] = "failed" if row["unexpected_axioms"] else "passed"
                        dependencies[row["name"]] = row
                        constants.append(row)
                        errors |= bool(row["unexpected_axioms"])
                report["environment_constants"] = sorted(constants, key=lambda row: row["name"])
                report["environment_constant_count"] = len(constants)
                errors |= lean.returncode != 0 or not constants
                for declaration in public:
                    row = dependencies.get(declaration["name"])
                    if row is None:
                        declaration["axiom_check"] = "missing_report"
                        errors = True
                    else:
                        declaration.update(axioms=row["axioms"], unexpected_axioms=row["unexpected_axioms"], axiom_check=row["axiom_check"])
                for item in report["selected_solution_proofs"]:
                    row = dependencies.get(item["declaration"])
                    item.update({key: row[key] for key in ("axioms", "unexpected_axioms", "axiom_check")} if row else {"axiom_check": "missing_report"})
                    errors |= item["axiom_check"] != "passed"
                if lean.returncode == 0:
                    checked = {d["name"]: d for d in public}
                    for declaration in declarations:
                        proof = TARGET_PROOFS.get(declaration["name"])
                        if proof and checked.get(proof, {}).get("axiom_check") == "passed":
                            declaration.update(classification="discharged_target_definition", closed_proof=proof)
                    for item in report["numbered_results"] + report["foundation_numbered_results"]:
                        item["closed_proof_check"] = "passed" if (checked.get(item["proof"], {}).get("axiom_check") == "passed" and
                            checked.get(item["target"], {}).get("classification") == "discharged_target_definition") else "failed"
                        errors |= item["closed_proof_check"] != "passed"
                report["lean_audit_status"] = "failed" if errors else "passed"
    counts = {}
    for declaration in declarations:
        counts[declaration["classification"]] = counts.get(declaration["classification"], 0) + 1
    report["declaration_counts"] = counts
    report["public_theorem_count"] = sum(d["classification"] == "proved_theorem" and not d["private"] for d in declarations)
    report["second_paper_public_theorem_count"] = sum(d["classification"] == "proved_theorem" and not d["private"] and d["file"].startswith("FRSB/") for d in declarations)
    report["coverage"] = ({"status": "not_run", "scope": "skipped_by_request", "errors": [], "entries": []} if args.skip_coverage
                          else check_coverage(root, declarations, report["lean_audit_status"] == "passed", paper))
    if not args.skip_coverage and (report["coverage"]["status"] == "failed" or (not args.scan_only and report["coverage"]["status"] != "passed")):
        errors = True
    report["external_paper_sha256"] = hashlib.sha256(paper.read_bytes()).hexdigest() if paper and paper.is_file() else None
    report["source_changed_during_audit"] = snapshot != source_snapshot(root)
    if report["source_changed_during_audit"]:
        errors = True
        report["lean_audit_status"] = "source_changed_during_audit"
    elif errors and report["lean_audit_status"] == "passed":
        report["lean_audit_status"] = "failed"
    report["status"] = "failed" if errors else "scanned_only" if args.scan_only else "formal_only_passed" if args.skip_coverage else "passed"
    report["finished_at"] = datetime.now(timezone.utc).isoformat()
    report_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({key: report.get(key) for key in ("status", "source_scan", "build_status", "lean_audit_status", "public_theorem_count", "environment_constant_count", "source_snapshot_sha256")}))
    print(f"Report: {report_path}")
    return int(errors)


if __name__ == "__main__":
    sys.exit(main())

DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?P<modifiers>(?:(?:public|private|protected|noncomputable|unsafe|partial)\s+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|opaque|structure|inductive|class|axiom|constant|instance)\s+"
    r"(?P<name>[^\s(:{]+)"
)


def mask_comments_and_strings(source: str) -> str:
    """Replace comments/strings by whitespace, retaining line/column locations."""
    out = list(source)
    i = 0
    depth = 0
    in_string = False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                out[i:i + 2] = "  "
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        elif in_string:
            if source[i] == "\\" and i + 1 < len(source):
                out[i] = " "
                if source[i + 1] != "\n":
                    out[i + 1] = " "
                i += 2
            else:
                if source[i] == '"':
                    in_string = False
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        elif source.startswith("/-", i):
            out[i:i + 2] = "  "
            depth = 1
            i += 2
        elif source.startswith("--", i):
            j = source.find("\n", i)
            if j == -1:
                j = len(source)
            out[i:j] = " " * (j - i)
            i = j
        elif source[i] == '"':
            out[i] = " "
            in_string = True
            i += 1
        else:
            i += 1
    return "".join(out)


def scan_sources(root: Path) -> tuple[list[dict], list[dict]]:
    declarations: list[dict] = []
    violations: list[dict] = []
    paths = set((root / "Paper").rglob("*.lean"))
    paths.update((root / "FRSB").rglob("*.lean"))
    if (root / "FRSB.lean").is_file():
        paths.add(root / "FRSB.lean")
    if (root / "Paper.lean").is_file():
        paths.add(root / "Paper.lean")
    if (root / "Solution.lean").is_file():
        paths.add(root / "Solution.lean")
    for path in sorted(paths):
        masked = mask_comments_and_strings(path.read_text(encoding="utf-8"))
        relative = str(path.relative_to(root))
        for match in FORBIDDEN.finditer(masked):
            violations.append({
                "file": relative,
                "line": masked.count("\n", 0, match.start()) + 1,
                "token": match.group(),
            })
        lines = masked.splitlines()
        scope: list[tuple[str, str]] = []
        for index, line in enumerate(lines):
            namespace = re.match(r"\s*namespace\s+([\w.]+)\s*$", line)
            section = re.match(r"\s*(?:@\[[^\]]*\]\s*)?(?:(?:public|private|noncomputable)\s+)*section(?:\s+([\w.]+))?\s*$", line)
            end = re.match(r"\s*end(?:\s+([\w.]+))?\s*$", line)
            if namespace:
                scope.append(("namespace", namespace.group(1)))
                continue
            if section:
                scope.append(("section", section.group(1) or ""))
                continue
            if end:
                if scope:
                    scope.pop()
                continue
            match = DECLARATION.match(line)
            if not match:
                continue
            name = match.group("name")
            if match.group("kind") == "instance" and name.startswith((":", "[", "{")):
                continue
            namespace_prefix = ".".join(n for kind, n in scope if kind == "namespace")
            qualified = name.removeprefix("_root_.") if name.startswith("_root_.") else ".".join(
                part for part in (namespace_prefix, name) if part
            )
            # The header ends before the definition/proof body.
            header = "\n".join(lines[index:])
            header = re.split(r":=|\bwhere\b", header, maxsplit=1)[0]
            is_prop_definition = match.group("kind") in {"def", "abbrev", "opaque"} and bool(
                re.search(r":\s*Prop\s*$", header)
            )
            is_private = "private" in match.group("modifiers").split()
            kind = match.group("kind")
            if kind in {"theorem", "lemma"}:
                classification = "proved_theorem"
            elif is_prop_definition and (name.endswith("Target") or qualified in TARGET_PROOFS):
                classification = "target_definition"
            elif is_prop_definition:
                classification = "proposition_definition"
            elif kind in {"def", "abbrev", "opaque"}:
                classification = "definition"
            else:
                classification = "type_declaration"
            declarations.append({
                "name": qualified,
                "kind": kind,
                "classification": classification,
                "private": is_private,
                "file": relative,
                "line": index + 1,
                "axiom_check": "pending" if not is_private else "transitive_only",
            })
    return declarations, violations


def scan_vendor_sources(root: Path) -> tuple[int, list[dict]]:
    paths = sorted((root / "vendor").rglob("*.lean"))
    violations: list[dict] = []
    for path in paths:
        masked = mask_comments_and_strings(path.read_text(encoding="utf-8"))
        for match in VENDOR_FORBIDDEN.finditer(masked):
            violations.append({
                "file": str(path.relative_to(root)),
                "line": masked.count("\n", 0, match.start()) + 1,
                "token": match.group(),
            })
    return len(paths), violations


def run_command(argv: list[str], root: Path, logfile: Path) -> subprocess.CompletedProcess:
    """Execute literal argv; no shell or string interpolation is involved."""
    result = subprocess.run(argv, cwd=root, text=True, capture_output=True, env=os.environ.copy())
    logfile.write_text(result.stdout + result.stderr, encoding="utf-8")
    return result


def check_coverage(root: Path, declarations: list[dict], checked: bool, paper: Path | None) -> dict:
    """Check every source-ledger entry, including the supporting displays.

    Semantic correspondence is recorded in the reviewable ledger. This check
    prevents missing entries, unresolved statuses, or nonexistent declarations
    from being packaged as completed coverage.
    """
    path = root / "results.json"
    if not path.is_file():
        return {"status": "not_run" if not checked else "failed",
                "errors": ["results.json is missing"]}
    ledger = json.loads(path.read_text(encoding="utf-8"))
    names = {d["name"]: d for d in declarations if not d["private"]}
    errors: list[str] = []
    groups = {"numbered_results": 26, "numbered_equations": 63, "unnumbered_displays": 69}
    expected_ids = {
        "numbered_results": {number.replace("_", ".") for number in NUMBERED_RESULT_IDS},
        "numbered_equations": {
            f"equation.{section}.{number}"
            for section, count in ((1, 16), (2, 20), (3, 7), (4, 9), (5, 8), (6, 3))
            for number in range(1, count + 1)
        },
        "unnumbered_displays": {f"display.{number}" for number in range(1, 70)},
    }
    source_lines = paper.read_text(encoding="utf-8").splitlines() if paper is not None and paper.is_file() else []
    if not source_lines:
        errors.append("External paper source is required; pass --paper-source ../paper-source/main.tex")
    allowed = {"proved", "definition", "cited_background", "prediction", "historical_context"}
    items: list[dict] = []
    for group, count in groups.items():
        entries = ledger.get(group, [])
        if len(entries) != count:
            errors.append(f"{group}: expected {count} entries, found {len(entries)}")
        ids = [entry.get("number") if group == "numbered_results" else entry.get("id")
               for entry in entries]
        if len(set(ids)) != len(ids) or set(ids) != expected_ids[group]:
            errors.append(f"{group}: duplicate, missing, or incorrect source identifiers")
        starts = [entry.get("source_start_line") for entry in entries]
        if len(set(starts)) != len(starts):
            errors.append(f"{group}: duplicate source locations")
        for entry in entries:
            label = entry.get("id", entry.get("number", entry.get("label", "unnamed")))
            status = entry.get("status")
            endpoints = entry.get("lean_declarations", [])
            item_errors: list[str] = []
            start, end = entry.get("source_start_line"), entry.get("source_end_line")
            quoted = entry.get("statement_latex" if group == "numbered_results" else "latex")
            if not (isinstance(start, int) and isinstance(end, int) and
                    1 <= start <= end <= len(source_lines) and isinstance(quoted, str) and
                    quoted and quoted in "\n".join(source_lines[start - 1:end])):
                item_errors.append("source quotation does not match its recorded paper location")
            if status not in allowed:
                item_errors.append(f"unresolved status: {status}")
            if status in {"proved", "definition"}:
                if not endpoints:
                    item_errors.append("no formal declarations mapped")
                for name in endpoints:
                    declaration = names.get(name)
                    if declaration is None:
                        item_errors.append(f"declaration not found: {name}")
                    elif checked and declaration.get("axiom_check") != "passed":
                        item_errors.append(f"declaration was not audited: {name}")
                if status == "proved" and endpoints and not any(
                    names.get(name, {}).get("kind") in {"theorem", "lemma"} for name in endpoints
                ):
                    item_errors.append("only definitions mapped to a claimed proof")
            elif status in allowed and not entry.get("coverage_note"):
                item_errors.append("background or prediction needs an explicit coverage note")
            if group == "numbered_results" and status != "proved":
                item_errors.append("numbered result lacks a proved paper conclusion")
            errors.extend(f"{group}/{label}: {error}" for error in item_errors)
            items.append({"group": group, "id": label, "status": status,
                          "declarations": endpoints,
                          "formal_check": "failed" if item_errors else ("passed" if checked else "not_run")})
    if paper is None or not paper.is_file() or hashlib.sha256(paper.read_bytes()).hexdigest() != ledger.get("paper", {}).get("source_sha256"):
        errors.append("paper source hash does not match the coverage ledger")
    return {"status": "failed" if errors else ("passed" if checked else "not_run"),
            "errors": errors, "entries": items}

