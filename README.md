An Euler-Faithful Lean 4 Formalization of the Basel Problem

Version: v1.0.0
Author: Bob Jefferson
ORCID: 0009-0003-1460-055X

This repository contains a Lean 4 formalization of the classical Basel identity:

sum_{n=1}^infinity 1 / n^2 = pi^2 / 6.

The proof is organized in an Euler-faithful manner. Two independent quadratic expansions of the normalized function

sin(pi z) / (pi z)

are derived:

A series-side expansion.

A product-side expansion via Euler’s product and logarithmic derivative control.

The quadratic coefficients are identified inside Lean to obtain the final result.

No new axioms are introduced.
No "sorry" placeholders remain.
The project builds cleanly under the pinned Lean toolchain.

The file EulerBasel/Audit/_Audit.lean prints the final theorem statements and their axiom dependencies during build for transparency. All reported axioms (propext, Classical.choice, Quot.sound) are standard classical axioms already present in mathlib.

Build and Verification

Recommended build procedure (PowerShell):

.\scripts\release-build.ps1

The script:

Prints Lean and Lake versions

Runs lake build

Stops on failure

Prints a success summary

If it finishes with:

[SUCCESS] Build completed with no errors.

then the formalization has been verified successfully.

Manual build (alternative):

lake build

A successful build confirms the formalization type-checks under the pinned toolchain.

Entry Point

The primary entry point is:

import EulerBasel

This imports the final assembly module and all required dependencies.

Project Structure

Lean source files:
EulerBasel/*.lean

Build configuration:
lakefile.lean
lean-toolchain

Documentation:
docs/euler_faithful_basel_lean.pdf

Release script:
scripts/release-build.ps1

Reproducibility

The repository is self-contained.

Verification requires only:

Lean 4 (as specified in lean-toolchain)

Lake build system

No external services are required beyond the initial mathlib cache fetch handled by Lake.

A successful build confirms correctness under the pinned toolchain.

Citation

If referencing this formalization, please cite the Zenodo DOI corresponding to this version.

Recommended citation format:

Jefferson, Bob. An Euler-Faithful Lean 4 Formalization of the Basel Problem. Lean 4 repository, version v1.0.0, 2026. DOI: 10.5281/zenodo.XXXXXXX.

License

See LICENSE file.
