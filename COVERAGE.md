# Paper coverage

The development concerns Patrick Lopatto's *Full replica symmetry breaking in the Sherrington–Kirkpatrick model*, [arXiv:2607.11756v4](https://arxiv.org/abs/2607.11756v4), revised 5 October 2026. The [source ledger](results.json) records exact mathematical text and locations from the supplied manuscript revision: `main.tex` SHA-256 `19f324d62868c129b2703574b1f23e18a875cbc18ab7ac121db3c34a57bdbcfa`. The public v4 source differs only in abstract reflow. Manuscript source is a separate companion to this repository, rather than part of its MIT-licensed original source tree.

The ledger contains 26 numbered results, 63 numbered equations, and 69 other mathematical displays. Its `status` field classifies mathematical entries and their supplied proof declarations; it does not by itself record a fresh successful build. Definitions, asserted results, cited background, historical context, and predictions are distinguished. [MATHEMATICS](MATHEMATICS.md) explains the selected headline definitions, normalization, proof route, and model scope.

## Numbered statements and exact targets

[NumberedResults](FRSB/NumberedResults.lean) defines each closed proposition `FRSB.Numbered.Statement_<section>_<number>` and supplies `FRSB.Numbered.result_<section>_<number>`. The targets are a mathematical correspondence with the paper, including stronger variants and supporting identities. They are not all literal copies of only the numbered environment's sentences. The source's standing β > 0 and zero-field conventions apply to the comparison below. Many analytic targets permit β ≠ 0, and some permit every real β; those variants cover the paper's domain without an additional assumption.

| Paper | Supplied coverage and exact-target qualification |
| --- | --- |
| Theorem 1.1 | The actual zero-field minimizer has support [0,q], a nonnegative density smooth through one-sided endpoint values, and a terminal atom c ∈ (0,1), with exact measure equality and total-mass normalization. |
| Theorem 1.2 | The exact quadratic terminal-mass inequality and both strict atom lower bounds. Quantified over all minimizers and all endpoints with the asserted interval support. |
| Proposition 2.1 | Joint continuity of spatial derivatives, measure-uniform positive-order bounds, evenness, sharp gradient and Hessian inequalities, and global uniform convergence of differences under weak measure convergence, including order zero. |
| Lemma 2.2 | Finite atomic weak approximants preserve left mass and singleton mass at every point of any finite set and converge in CDF L¹ distance. |
| Lemma 2.3 | The exact same-Brownian uniform state estimate and weak-measure convergence of every fixed polynomial jet moment. Countably generated filters extend the sequence formulation. |
| Lemma 2.4 | Cole–Hopf and zero-mass heat evolution, plus the actual state-law h-transform formula with initial time zero permitted. |
| Lemma 2.5 | Bounded magnetization martingale, adapted Brownian left-sum convergence at each fixed terminal time, Γ derivatives and interval identities, and all polynomial moment closure. Derivative identification of the named Γ″ and Γ‴ sources is restricted to constant-CDF interior intervals. |
| Lemma 2.6 | Γ(q) = q and Γ′(q) ≤ 1 at every support point of every actual minimizer. The minimization premise is the global minimum of the constructed PDE functional. |
| Lemma 2.7 | Nonnegativity of bounded classical supersolutions on the line or half-line with the stated outward drift and zeroth-order upper bounds. The target allows T = 0 and the pointwise differentiability needed by the proof. |
| Proposition 3.1 | All backward inequalities, bounded fields, and uₓₓₓ ≤ 0 on the nonnegative half-line. The target also covers CDF mass zero and supplies auxiliary-field smoothness. |
| Remark 3.2 | The six inverse-magnetization identities and time monotonicity conclusions are in `Statement_3_2`. The explicit nonpositive square-root susceptibility slope and rate signs are additionally in [backward_magnetization_rates](FRSB/BackwardsSusceptibilitySigns.lean). |
| Lemma 3.3 | Relative derivative bounds through orders 2–5 and rational-field bounds, extended from finite atomic measures to every measure. |
| Lemma 3.4 | Actual constant-CDF interior PDEs, genuine singleton mass updates, unchanged-z algebra, and terminal values. Constant-CDF intervals of arbitrary measures extend the finite atomic setting. |
| Proposition 4.1 | The actual state law has a positive smooth even density. Both endpoint gauges, derivative/slope/curvature/third-derivative bounds, both tails, and local all-order convergence are covered, including every preserving weak sequence. |
| Lemma 4.2 | The exact Gaussian bridge heat step takes the value after the left endpoint's possible atom and before the right endpoint's possible atom. The target extends to arbitrary measures with zero open-interval mass. Its separate evenness sentence is supplied by [forwardBridgeCorrection_even](FRSB/ForwardBridgeParity.lean) and [forwardBridgeLeftCorrection_even](FRSB/ForwardLeftAtoms.lean). |
| Lemma 4.3 | Uniform bounds for each finite collection of positive spatial derivative orders, including both atom gauges, extended to every measure. |
| Proposition 5.1 | Γ″ = 0 implies Γ‴ > 0 on positive constant-CDF interiors. The target also contains the positive normalized covariance representation. |
| Lemma 5.2 | The actual material derivatives, log-density transport, weight transport, and centered identity with their rescaled clocks. The target also covers mass zero. |
| Remark 5.3 | Actual inverse-coordinate identities, density/law change of variables, Jacobian, weighted-coordinate PDE, scores, and centering. The general prose chain-rule observation for any smooth F is not a separate universal-F theorem; its displayed concrete applications are proved. |
| Lemma 5.4 | Compact-time Gaussian domination of the actual forward-clock derivatives, bounded transported fields, and zero origin fluxes. |
| Lemma 5.5 | Strict Φ, K, and Ψ monotonicity and nonstrict H monotonicity. Some targets extend to individual times outside constant-positive-mass intervals; Φ and Ψ retain positive mass. |
| Corollary 5.6 | Γ′ strictly decreases then strictly increases on the constant-positive-mass interval, with either piece permitted to be empty. |
| Proposition 6.1 | Every zero-field minimizer at β > 1 has support exactly [0,q], with 0 < q < 1. |
| Lemma 6.2 | The actual CDF below q and left mass at q equal the continuous positive-denominator moment quotient, and there is no atom at zero. |
| Lemma 6.3 | The quotient and every polynomial positive-spatial-derivative moment are smooth through one-sided endpoint values on [0,q]. |
| Remark 6.4 | The SK half-open CDF smoothness and all-order terminal endpoint improvement. The cited general mixed-p-spin theorem is separately classified as background. |

## Mathematical conventions and limits

The probability measures are actual Borel probability measures on [0,1]. Their real-image topological support is distinct from their set of atoms. The paper's ordered-pair Hamiltonian includes diagonal couplings and coefficient β/√(2N); [OrderedSKFiniteInput](FRSB/OrderedSKFiniteInput.lean) proves its bridge to the earlier increasing-pair realization and its Parisi formula. Minimizer existence follows from compactness and continuity; uniqueness is proved for zero field and β ≠ 0 by strict convexity.

The underlying probability realization is the projective Gaussian space `ℝ≥0 → ℝ` carrying a continuous Brownian modification and its natural filtration. The Wiener measure on continuous paths is a pushforward. The optimal state is the concrete Brownian-driven pathwise integral solution at initial field zero. The stochastic differential for its magnetization is represented by canonical adapted uniform Brownian left sums with convergence in measure at each terminal time, with supporting L² residual estimates. The development does not assert a theorem for every filtered probability space, every choice of stochastic-sum partitions, or usual filtration augmentation.

The forward density represents the actual state law. Its proof uses finite conditional kernels, tilted Brownian histories, Gaussian bridge disintegration, and weak-measure passage. The normalized crossing weight is 2pC² on the half-line. Restricting the Lebesgue density to (0,∞) rather than [0,∞) changes no mass. Physical time s, forward time β²s, and backward time β²(1−s) are explicit. A constant translation of the backward clock used on an interval changes no derivative formula.

Closed-interval smoothness uses derivatives within the interval. The actual CDF jumps at q; smoothness is asserted below that atom, while its moment quotient, density, and all their derivatives extend to q from the left. The density is nonnegative; pointwise strict positivity throughout [0,q] is not claimed.

The introduction's general mixed-p-spin statements, zero-temperature limits, near-critical and low-temperature asymptotics, historical results, and physics predictions are context or cited background. The general mixed-model result in Remark 6.4 is not a newly proved general-model theorem. The selected results concern zero-field SK at finite β > 1.

The retained `Paper` modules include the earlier positive-field AT development and reusable conditional assembly lemmas. `Paper`'s numbered statements refer to that earlier paper. A conditional theorem with a variational criterion, law identity, uniqueness claim, or free-energy limit as a premise proves the stated implication. A proposition-valued target is a definition, not a proof. These categories are distinct from the closed FRSB theorem declarations and their proved concrete dependencies.

## Verification evidence

[NumberedResultsAudit](FRSB/NumberedResultsAudit.lean) contains typed assignments for all 26 exact Lean targets and code that rejects transitive axioms other than `propext`, `Classical.choice`, and `Quot.sound`. The source comparison above separately records the relation of those targets to the paper, including the additional declarations for 3.2 and 4.2 and the 5.3 qualification.

Fresh build, axiom, metadata, source-limit, Comparator, and independent kernel outcomes must be read from the source-revision verification record generated by the repository's verification tools. Historical build logs and prior audit success assertions are not evidence for this prepared revision. Automated source comparison and review do not establish human mathematical review.
