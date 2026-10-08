# Mathematical correspondence and scope

This development concerns Patrick Lopatto's *Full replica symmetry breaking in the Sherrington–Kirkpatrick model*, [arXiv:2607.11756v4](https://arxiv.org/abs/2607.11756v4), revised 5 October 2026. The source ledger records the supplied manuscript's exact statement text and line numbers. That manuscript's `main.tex` has SHA-256 `19f324d62868c129b2703574b1f23e18a875cbc18ab7ac121db3c34a57bdbcfa`; the public v4 source has SHA-256 `9adf4431c3f6d0a0c8cd566dfab40d45b2fb3e763be8a9794a38ea43c969ee52`. Their difference is abstract reflow, with the mathematical statements unchanged. The bibliography has SHA-256 `cb4b6bb87c105ff75924ac92ffaf9e80db58cff0c45290a3b552dbf80fa40681` in both versions. Manuscript sources are distributed separately from the repository's MIT-licensed original code and documentation.

## The selected results

For every real inverse temperature β > 1 at zero external field, Theorem 1.1 states that the unique Parisi minimizer μ has support [0,q], where 0 < q < 1, and decomposes as a nonnegative smooth density below q together with a terminal atom c, where 0 < c < 1. The formal statement includes the exact measure equality on the real line, c = μ({q}), and the normalization ∫₀ᑫρ(s) ds + c = 1. Support means topological support of the probability measure; it does not mean its set of atoms. The theorem does not assert that the density is strictly positive at every point.

Theorem 1.2 sets m = 1 − c and proves

\[
m\left(4-m+\frac{1}{\beta^2q}\right)\leq 2,
\qquad c>\max\{\sqrt{2}-1,\;1-2\beta^2q\}.
\]

The submission interface states the first conclusion as the existence of a measure with the asserted form that minimizes the functional, together with equality of every other minimizer to that measure. It states the second conclusion for every minimizing measure and every endpoint q with support [0,q]. This quantification makes the relation to the chosen minimizer explicit. It introduces no further assumption on β, the PDE, the diffusion, or the support: the existence of such an interval is the first theorem's conclusion. The quantitative theorem's interval hypothesis specifies the endpoint to which the bound applies.

| Manuscript result | Development theorem | Mathematical meaning |
| --- | --- | --- |
| Theorem 1.1 | `FRSB.fullRSB`, `FRSB.fullRSB_of_minimizer`, `FRSB.fullRSB_unique` | Exact smooth-density and atom decomposition, interval support, and minimizing-measure uniqueness. |
| Theorem 1.2 | `FRSB.quantitative_atom` | Quadratic terminal-mass inequality and both strict atom lower bounds. |
| Proposition 6.1 | `FRSB.Numbered.result_6_1` | Every zero-field minimizer at β > 1 has support exactly [0,q], with 0 < q < 1. |
| Lemmas 6.2–6.3 | `FRSB.Numbered.result_6_2`, `FRSB.Numbered.result_6_3` | The CDF below the atom equals a positive-denominator moment quotient, has no atom at zero, and its left extension and all polynomial jet moments are smooth on [0,q]. |
| Remark 6.4, SK conclusion | `FRSB.Numbered.result_6_4` | CDF smoothness on [0,q) and continuous derivatives of every order of the left quotient, density, and moments up to q. |

The [numbered targets](FRSB/NumberedResults.lean) provide closed proposition types and corresponding proof declarations for all 26 numbered statements. The [source ledger](results.json) also records numbered equations, other displays, and cited background. A proposition-valued `Statement_*` or `*Target` definition states an obligation; its corresponding theorem supplies the proposed proof. A type assignment checks a proof against its Lean target, while the mathematical source comparison checks whether that target expresses the manuscript claim. Some sentences are mapped to additional declarations: Remark 3.2's nonpositive square-root susceptibility slope is in `FRSB.backward_magnetization_rates`, and Lemma 4.2's evenness conclusion is in `FRSB.forwardBridgeCorrection_even` and `FRSB.forwardBridgeLeftCorrection_even`. Remark 5.3's general chain-rule observation for an arbitrary smooth function is not separately exposed as a universal-function theorem; its displayed concrete applications and the density and PDE identities are formalized. See [COVERAGE](COVERAGE.md) for these qualifications.

## Concrete definitions and normalization

`Paper.ParisiMeasure` is `ProbabilityMeasure (Set.Icc (0 : ℝ) 1)`. Its CDF is the actual mass μ([0,s]), including the mass at s. The [Parisi functional](Paper/RSFunctional.lean) is

\[
\mathcal P_\beta(\mu)=\log 2+u_\mu(0,0)
-\frac{\beta^2}{2}\int_0^1s\,\mu([0,s])\,ds,
\]

with terminal value u(1,x) = log cosh x and backward equation

\[
u_s+\frac{\beta^2}{2}(u_{xx}+\mu([0,s])u_x^2)=0.
\]

[Challenge](Challenge.lean) defines the time-zero PDE value directly from continuous weak potentials with a bounded measurable distributional spatial gradient and this terminal-value equation. It takes the infimum of their time-zero values. [Solution](Solution.lean) identifies that set of values as a nonempty singleton at every β > 1, using the constructed potential and its unrestricted weak uniqueness theorem. Thus no existence or uniqueness premise is supplied to the submission theorem. The convention for the infimum of an empty set is irrelevant on the theorem's domain.

The substantive development [constructs the potential](Paper/ParisiSolution.lean) from genuine finite Cole–Hopf grid gradients and proves that it solves the [weak PDE](Paper/ParisiPDE.lean). [Weak well-posedness](Paper/ParisiWeakWellPosed.lean) identifies every continuous weak potential in the stated bounded-gradient class with this construction on the closed strip. It requires no additional growth, smoothness, or mild-equation hypothesis. The minimizing measure is then [constructed using compactness and continuity](FRSB/ParisiMinimizer.lean). [Strict convexity](FRSB/ParisiStrictConvexity.lean) proves its uniqueness at zero field for β ≠ 0, which covers every selected β > 1. The paper cites these background facts; the formal development proves the versions it uses.

The [literal finite-volume Hamiltonian](FRSB/OrderedSKFiniteInput.lean) uses every ordered pair, including diagonal terms, independent standard Gaussian couplings, and coefficient β/√(2N), as in the paper. The equality of its expected free energy with the earlier increasing-pair realization and its Parisi formula are separate proved bridge results. The increasing-pair realization alone should not be read as the paper's displayed ordered-pair Hamiltonian.

The physical overlap clock is s ∈ [0,1]. Forward heat time is β²s. Backward time is β²(1−s); the paper sometimes translates this clock to β²(q₁−s) on a particular interval. The translation has no effect on derivative identities. The factors β², β⁴, and β⁶ in moment and Γ derivative formulas are retained explicitly.

## Probability realization and proof route

The underlying probability space is the projective Gaussian space `BrownianSample = ℝ≥0 → ℝ`, with measure `gaussianLimit`. [CanonicalBrownian](Paper/CanonicalBrownian.lean) supplies an everywhere-continuous Brownian modification starting at zero, and its pushforward to continuous paths defines a Wiener measure. The state is the actual pathwise integral solution driven by that Brownian process, starting at zero. The filtration is its natural filtration. No separate theorem on usual filtration augmentation, or transfer to every possible filtered probability space, is asserted.

The bounded magnetization process is a genuine martingale. Its Brownian stochastic identity is expressed through adapted left sums with convergence in measure; supporting results establish the L² residual estimates. The forward density represents the actual state law, rather than an independently supplied candidate density. Finite conditional laws, Gaussian bridge disintegration, and weak-measure passage establish that identification.

The main proof follows the manuscript's structure: backward and forward shape inequalities imply that Γ″ can only cross zero upward on a positive constant-mass interval; the minimizing-measure optimality conditions then rule out support gaps; the CDF moment quotient gives endpoint smoothness and the exact density; the terminal profile and a normalized weighted law give the atom inequality. The formalization additionally constructs and proves several analytical and probabilistic facts that the paper cites or treats as background. These additional proofs are dependencies, rather than extra hypotheses of the headline results.

Some numbered targets contain strengthenings: many analytic statements are proved for β ≠ 0 rather than only β > 0, several results initially formulated for finite atomic measures are proved for all measures, and targets include supporting conclusions from the surrounding proof. These differences should be read from the exact types and the coverage table; a numbered target is not a literal transcription of only the theorem environment.

## Endpoint and model scope

Smoothness on the closed support interval uses derivatives within that interval. It expresses the manuscript's continuous extension of every interior derivative and its one-sided endpoint values. The actual CDF jumps at the terminal atom q. It is smooth on [0,q), while its moment quotient and density extend smoothly to q from the left. No smoothness through the jump is asserted.

The submitted headline results concern the zero-field SK model at every finite β > 1. They do not assert the analogous statement at nonzero external field or for general mixed p-spin models. The general mixed-model theorem cited in Remark 6.4, zero-temperature claims, β → ∞ limits, near-critical expansions, and numerical predictions are cited background or context. They are not additional submitted results.

The retained HJB value-function representation uses bounded continuous adapted controls whose magnitude is at most one. Its classical Dirac time regularity is restricted away from the CDF interface q, with within-strip endpoint derivatives. Those are supporting theorem scopes; the selected weak-PDE headline formulation retains no control-class premise.

The retained `Paper` library contains the prior positive-field AT development. Its targets and numbered results refer to that earlier paper, not to the 26 numbered statements of the present manuscript. It also contains reusable conditional assembly lemmas, such as [ConditionalMain](Paper/ConditionalMain.lean), whose variational criterion, law, uniqueness, or free-energy-limit hypotheses remain visible in their theorem types. Those lemmas prove implications. They must not be described as unconditional results solely because they compile. The selected FRSB proofs instead use the constructed PDE, genuine diffusion, and discharged minimizing-measure inputs.

The semantic comparison and subsequent repository preparation were automated Codex work. Authorship and maintainer responsibility do not establish human mathematical review. Fresh compiler, exact-target, transitive-axiom, Comparator, and independent kernel-check outcomes are recorded in the repository's verification record and tied to its source revision; this document is a description of mathematical correspondence, not an independent certification of those outcomes.
