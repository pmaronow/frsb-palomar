# Reproducible local verification

Run the commands from the repository root after installing the pinned Lean
toolchain. Python 3.11 or newer is required. Metadata checking uses
`PyYAML==6.0.3` and `jsonschema==4.26.0`.

```sh
python3 -m pip install -r tools/requirements.txt
python3 tools/submission_check.py --sources-only
lake exe cache get
python3 tools/submission_check.py --require-local-mathlib --report ../verification/submission-preflight.json
python3 tools/build_all.py --report ../verification/build-all.json
python3 tools/audit.py --no-build --paper-source ../paper-source/main.tex --report ../verification/audit-report.json
python3 tools/comparator_check.py --report ../verification/comparator.json
```

`build_all.py` enumerates every submitted Lean file, including vendored modules
outside the aggregate import closure. `lake build FRSB Paper Challenge Solution`
builds the selected interfaces and aggregates, but does not by itself establish
that every unused vendor source builds.

`audit.py` scans original sources for proof holes and forbidden axioms, permits
only the two selected `by sorry` Challenge theorem bodies, and checks transitive
axioms of all original-module constants visible in the imported environment.
This includes instances and generated declarations. It also typechecks the
twenty-six numbered FRSB proofs and fifteen foundation proofs against their exact
targets. The coverage ledger's source quotations and locations are checked
against the separately supplied manuscript; an absent or mismatched manuscript
fails the coverage check. This formal audit cannot establish mathematical
fidelity or human review.

The CI proof job explicitly uses `--skip-coverage` because the manuscript is an
external companion. That limited run records `formal_only_passed`, with coverage
`not_run`, and cannot support the complete packaging check.

`submission_check.py` checks metadata against the vendored schema, source
limits, module headers, dependency pins, resolved Mathlib revision/toolchain,
direct Challenge imports and shadowing, conventional license text, and local
documentation links. The official Palomar verifier authenticates dependencies
and the transitive Challenge closure independently. The local classification
check supports this project's selected codes only.

`comparator_check.py` runs `verify_comparator.sh`, records the result and requires
acceptance by Lean, NanoDa and con-ron. The shell script requires bubblewrap and
the toolchain-bundled `leanexport`, `leanchecker`, `nanoda_bin` and `con-ron`.
Missing executables, sandbox failures, rejected kernels, missing acceptance
markers, or changed sources fail the check. The submitted Comparator config
cannot supply its own external kernel commands; the wrapper creates a protected
temporary runtime config using the installed toolchain executables.

Reports and raw logs default to `../verification`, outside the public source
tree. Every structured report records source SHA-256 hashes and an inventory
digest. Only the generated root `VERIFICATION.md` evidence summary is excluded
from this checked inventory to avoid a self-referential hash; the source archive
and its archive SHA-256 still include it. No historical report is treated as a
pass for the current source.

To copy the clean repository and produce a source-only archive after all four
reports pass:

```sh
python3 tools/package.py --output ../deliverables
```

The packager excludes Git internals, caches, generated evidence directories,
temporary files, build products and raw logs. It refuses stale or incomplete
verification by default. `--allow-unverified` permits an explicitly marked
delivery and lists the outstanding checks in a companion manifest; it does not
turn them into passes. The manuscript is supplied separately and is never added
to the public repository or source archive.

The source and metadata preflight and Comparator shell wrapper are adapted from
[pmaronow/at-palomar](https://github.com/pmaronow/at-palomar), revision
`915bca99f46bad65629ef35c8be4bf8fc962af9a`, under its MIT license (copyright
2026 P. M. Aronow and Patrick Lopatto). Original verification tooling and these
adaptations are covered by the repository's MIT license. The third-party
metadata schema retains its separate Apache-2.0 license under
[`vendor/verification-metadata`](../vendor/verification-metadata/README.md).
