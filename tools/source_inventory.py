#!/usr/bin/env python3
"""Shared source inventory: generated evidence is never a public source file."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess

EXCLUDED_DIRECTORIES = {".git", ".lake", "work", "audits", "__pycache__", ".pytest_cache"}
EXCLUDED_SUFFIXES = {".pyc", ".pyo", ".tmp", ".log", ".zip", ".tar", ".gz",
                     ".olean", ".ilean", ".ir", ".a", ".bc", ".dll", ".dylib", ".o", ".obj", ".so", ".trace"}
EXCLUDED_NAME_ENDINGS = (".olean.private", ".olean.server")
# This human-readable evidence record is written after verification. Excluding
# only this file prevents self-referential source hashes; archives still include
# it and their own SHA-256 binds every delivered byte.
EXCLUDED_EVIDENCE_FILES = {"VERIFICATION.md"}


def candidate_files(root: Path):
    for directory, subdirectories, names in os.walk(root, followlinks=False):
        here = Path(directory)
        subdirectories[:] = sorted(name for name in subdirectories
            if name not in EXCLUDED_DIRECTORIES and not (here / name).is_symlink())
        for name in sorted(names):
            path = here / name
            if (path.is_file() and not path.is_symlink() and path.suffix not in EXCLUDED_SUFFIXES
                    and not path.name.endswith(EXCLUDED_NAME_ENDINGS)):
                yield path


def source_snapshot(root: Path) -> dict[str, str]:
    return {path.relative_to(root).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(candidate_files(root))
            if path.relative_to(root).as_posix() not in EXCLUDED_EVIDENCE_FILES}


def snapshot_digest(snapshot: dict[str, str]) -> str:
    encoded = json.dumps(snapshot, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def revision(root: Path) -> dict:
    def git(*arguments):
        result = subprocess.run(["git", *arguments], cwd=root, text=True, capture_output=True)
        return result.stdout.strip() if result.returncode == 0 else None
    return {"git_commit": git("rev-parse", "HEAD"),
            "git_tree": git("rev-parse", "HEAD^{tree}"),
            "git_dirty": bool(git("status", "--porcelain")),
            "identity_note": "source_snapshot_sha256 identifies the exact checked candidate excluding generated evidence VERIFICATION.md; archive SHA-256 binds all delivered files"}
