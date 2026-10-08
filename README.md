# Full replica symmetry breaking in the SK model

Lean 4 formalization of Patrick Lopatto's [Full replica symmetry breaking in the Sherrington–Kirkpatrick model](https://arxiv.org/abs/2607.11756v4). The project studies the actual zero-field Parisi minimizing probability measure on [0,1] at every inverse temperature β > 1.

P. M. Aronow and Patrick Lopatto are the formalization authors and responsible maintainers. Patrick Lopatto is the paper author. Sol 6.1 autoformalized the original development. Subsequent Codex preparation, compiler compatibility work and automated review are disclosed separately in [formalization.yaml](formalization.yaml). These attributions do not imply human mathematical review.

## Results

[Challenge.lean](Challenge.lean) independently states the two headline results using concrete definitions and Mathlib imports. [Solution.lean](Solution.lean) supplies corresponding proofs; [comparator.json](comparator.json) selects:

- `PalomarFRSB.fullRSB` (Theorem 1.1): there is a unique Parisi minimizer. Its support is [0,q] for 0 < q < 1, and it is the sum of a nonnegative density smooth on the closed interval and an atom of mass 0 < c < 1 at q.
- `PalomarFRSB.quantitativeAtom` (Theorem 1.2): for m = 1 − c, the actual terminal atom satisfies m(4 − m + 1/(β²q)) ≤ 2 and c > max{√2 − 1, 1 − 2β²q}.

The Challenge defines the Parisi functional from continuous potentials and bounded weak spatial gradients satisfying the terminal PDE with coefficient β²/2 and terminal value log cosh. The infimum of their time-zero values is proved equal to the constructed solution value on the theorem domain. Existence and uniqueness are proved in the supporting development, rather than assumed in the headline statements.

[FRSB/](FRSB/) contains the substantive full RSB development. [Paper/](Paper/) supplies the earlier Parisi PDE, diffusion, control and physical-model foundation. [COVERAGE.md](COVERAGE.md), [MATHEMATICS.md](MATHEMATICS.md) and [results.json](results.json) describe the twenty-six numbered results, supporting displays, proof routes and scope differences. Proposition-valued targets are specifications; their designated `result_*` declarations supply proofs.

## Installation and verification

The build pins Lean 4.35.0-rc2 and Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`, with all dependency revisions in [lake-manifest.json](lake-manifest.json). Install the pinned Lean toolchain through [elan](https://github.com/leanprover/elan); Linux Comparator verification also requires `bwrap`. Python validation dependencies are pinned in [tools/requirements.txt](tools/requirements.txt).

Run from the repository root:

```sh
python3 -m pip install -r tools/requirements.txt
lake exe cache get
python3 tools/submission_check.py
python3 tools/build_all.py --report ../verification/build-all.json
python3 tools/audit.py --paper-source ../paper-source/main.tex --report ../verification/audit-report.json
python3 tools/comparator_check.py --report ../verification/comparator.json
```

The manuscript companion in the local delivery contains the exact source used for the coverage ledger. The proof build and Comparator do not require the manuscript. See [VERIFICATION.md](VERIFICATION.md) for completed checks, failures, source identity and reproduction details. The two intentional theorem `sorry` placeholders in Challenge are permitted statement holes. Solution and its proof dependencies must contain only `propext`, `Classical.choice` and `Quot.sound`, with no proof holes or forbidden reduction axioms.

The audit checks transitive axioms of public project declarations and assigns each numbered proof to its exact target. Comparator checks statement and definition agreement with Lean and the independent NanoDa and con-ron kernels. Local checks do not replace Palomar's trusted verification and editorial review.

## Mathematical scope

The Hamiltonian normalization is β/√(2N) over all ordered pairs, including the independent centered diagonal contribution. The physical-model bridge proves agreement with the imported Parisi formula. The selected results concern zero external field and β > 1; the manuscript's mixed-model history and physics predictions are background.

Closed-interval density smoothness includes one-sided endpoint derivatives. It does not assert smoothness through the terminal CDF jump. The diffusion is constructed on a concrete projective Gaussian probability space carrying a continuous Brownian modification with its natural filtration. No general transfer to a completed, right-continuous augmented filtration is asserted. General time derivatives are weak; classical identities are established on constant-CDF intervals. The retained HJB representation uses bounded continuous adapted controls of magnitude at most one. Further supporting scope restrictions and strengthenings are recorded in MATHEMATICS.md.

The support proof uses a strict covariance identity at zeros of Γ″ and a proved scalar crossing argument. The manuscript's full transport representation is also retained as a separately proved supporting result. Vendored proof foundations, their exact revisions and prior adaptations are recorded in [PROVENANCE.md](PROVENANCE.md); [compatibility/](compatibility/) records the subsequent compiler port.

## Licensing

Original code and project documentation are [MIT licensed](LICENSE). Vendored Lean sources retain their Apache-2.0 licenses and notices; validation assets retain their own terms. The manuscript has separate distribution terms and is cited here. Its source and bibliography are supplied as a separate local companion, outside the public software source tree. Quoted manuscript statements in the coverage ledger retain their source attribution.
