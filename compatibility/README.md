# Lean compiler compatibility

The supplied development used Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The prepared repository pins Lean 4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`, matching the reference repository and the current minimum supported Palomar toolchain.

[module-system.patch](module-system.patch) records the module-system migration against the supplied Lean sources: module headers, public imports, exposed public sections and explicit visibility of helpers referenced across modules. Declaration visibility is broadened where needed for the new module system; mathematical statements and hypotheses are preserved.

[compiler-port.patch](compiler-port.patch) records elaborator and API repairs after the module migration. The repairs preserve the mathematical definitions and theorem statements, with explicit witnesses, inference arguments or equivalent proof steps. The patch includes any subsequent compatibility corrections required by the full build.

Prior upstream adaptation patches remain in their vendored directories. They describe the supplied foundation slices; these two patches describe the later compiler port. They do not introduce custom axioms or proof placeholders. The independent Challenge and Solution are new interface modules, rather than part of either compatibility patch. Build and proof-audit outcomes are recorded for the final source identity in [VERIFICATION.md](../VERIFICATION.md).
