# Verification record

Local verification of the prepared source completed on 8 October 2026. The checks below apply to source commit `faec01d2406b93dda79d3c6adfebe87340b706b8`, tree `cab45b751ab1587a0ea88447ed126d78c462d90c`. The checkout was clean when each check began, and the checked inputs did not change during execution.

The checked source inventory contains 1,030 files and has SHA-256 `8fc7c3315d1fcb467ee365662ee5ed698358ca7df6997e79d88c44ccf6d1f1fc`. [source_inventory.py](tools/source_inventory.py) hashes the sorted path-to-file-digest map. It excludes build artifacts, Git internals and this generated record. The later reporting commit changes only this record; the delivered archive's SHA-256 binds every packaged file, including this record. Evidence JSON and checksums accompany the local delivery outside the public source tree.

## Completed checks

| Check | Outcome and scope |
| --- | --- |
| Complete source build | **Passed:** all 985 submitted Lean modules, including the retained vendored sources, Challenge and Solution. Lean 4.35.0-rc2, commit `11acb17ec6b07a8f9e9173e6845197929540936b`; Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. |
| Transitive axiom audit | **Passed:** 5,600 imported project constants from FRSB, Paper and Solution, including generated declarations and instances. Each selected Solution theorem has exactly `propext`, `Classical.choice` and `Quot.sound`; no unexpected axioms. |
| Exact target assignments | **Passed:** all 48 designated proof assignments, including 26 current-paper numbered targets and 15 retained earlier-paper numbered targets. Proposition-valued targets were checked through their designated typed proofs, rather than counted as proofs by themselves. |
| Source and Challenge holes | **Passed:** no forbidden tokens in original Solution/development sources or 465 vendored Lean sources. Challenge has exactly two intentional theorem `by sorry` bodies, one for each selected result; it is not imported by Solution. |
| Source ledger | **Passed:** all 158 entries (26 numbered results, 63 equations, 69 other displays), their source quotations and locations, declaration mappings, and recorded status categories. External manuscript SHA-256 `19f324d62868c129b2703574b1f23e18a875cbc18ab7ac121db3c34a57bdbcfa`. This mechanical check complements the separately documented automated semantic comparison. |
| Comparator | **Passed:** selected statement/definition agreement and exported proofs accepted by the Lean default kernel, NanoDa and con-ron. Comparator exited with code 0 and reported `Your solution is okay!`; all three required acceptance markers were present. |
| Metadata and repository structure | **Passed:** local preflight and current upstream metadata contract, v0.4 schema, Comparator configuration, license structure and licensee 10.0.0 MIT detection. |
| Module headers and limits | **Passed:** native header parsing and official source scan for all 985 Lean files. Largest source: 6,363 lines, below 10,000. Challenge: 137 lines / 6,434 bytes, below both hard and warning thresholds. At the checked commit, the source tree occupied 13,651,805 bytes, below 500 MiB. |
| Challenge imports | **Passed:** five permitted Mathlib direct imports, no project shadowing, and recursively checked permitted closure of 4,182 source modules: 1,408 Lean core, 2,517 Mathlib and 257 dependency modules. |
| Dependency pins and source integrity | **Passed:** nine fixed dependency commits, local tracked-source integrity, canonical commit/tree evidence and compatible Mathlib ancestry; exact Mathlib manifest/toolchain consistency. |
| Documentation links | **Passed:** 57 relative documentation links in the local structural preflight. |

The source scanner identifies 3,695 public theorem/lemma declarations in the original project, including 1,762 in FRSB. Counts of source declarations and generated environment constants describe different inventories. The audit used `--no-build` after the separate exhaustive build; its build field is `skipped_by_request`, while the complete build report records the successful build. Reports identify these scopes individually.

The policy snapshot is recorded in [PROVENANCE.md](PROVENANCE.md): PalomarPolicy `96b034cc31a72a63d4f4041911dce337a85c9a04`, PalomarSubmission `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, and metadata schema `99c678e569c7c4c0772db297c5ddd5e4c9b6322e`. The official local preparation checks used the native Lean module parser and Palomar's pinned license detector in addition to this repository's lightweight preflight.

## Reproduction

Follow the installation commands in [README.md](README.md). With the checksum-pinned manuscript companion beside the repository, run:

```sh
python3 tools/submission_check.py --require-local-mathlib --report ../verification/submission-preflight.json
python3 tools/build_all.py --report ../verification/build-all.json
python3 tools/audit.py --no-build --paper-source ../paper-source/main.tex --report ../verification/audit-report.json
python3 tools/comparator_check.py --report ../verification/comparator.json
python3 tools/package.py --output ../delivery --name frsb-palomar
```

The build and proof/kernel checks do not require the manuscript. Omitting coverage with `--skip-coverage` yields `formal_only_passed`, not a complete verification pass; `--scan-only` also does not claim Lean verification. Default packaging rejects incomplete or stale reports. Raw logs and generated audit sources remain outside the public repository.

[Comparator tooling](tools/verify_comparator.sh) uses the pinned toolchain's Lean, NanoDa and con-ron executables. It supplies kernel commands through a runtime configuration, rather than allowing submitted `external_kernels`; con-ron runs with two jobs. The JSON report records executable hashes, return status and each required acceptance marker.

## Interpretation and remaining limits

No outstanding local build, axiom-audit, exact-target, Comparator or independent-kernel blocker remains for the selected interface. This conclusion applies to the checked formal statements and their dependencies; the source correspondence qualifications below remain material.

The two headline results concern the zero-field SK model at finite β > 1. [MATHEMATICS.md](MATHEMATICS.md) and [COVERAGE.md](COVERAGE.md) preserve the concrete probability realization, natural filtration, stochastic-sum scope, weak/classical time distinctions, one-sided smoothness, supporting domain strengthenings, alternative crossing proof route, and the qualification concerning Remark 5.3's general chain-rule prose. Conditional infrastructure retains its explicit hypotheses. Background citations and predictions are not asserted as newly proved results.

The original autoformalization was performed by Sol 6.1. Subsequent preparation, compiler repairs and semantic review were automated Codex work, disclosed separately in [formalization.yaml](formalization.yaml). Compatibility changes preserve mathematical statements and are recorded in [compatibility](compatibility/). Authorship and responsible-maintainer attribution do not establish human mathematical review.

These are local verification results, not Palomar protected verification receipts or source-preservation attestations. Publication, submission, registration and editorial approval have not occurred. Palomar may repeat source authentication, dependency and import checks, proof checking, metadata checks and editorial review under its then-current requirements.
