# Validation

The repository was checked on 25 October 2026 with Lean 4.35.0 and the dependencies fixed in `lake-manifest.json`.

- All 423 research source modules were rebuilt from source in a new working directory. Dependency build caches were reused at the recorded commits.
- The integrated audit checked the exact types and axiom dependencies of all 2,634 named declarations.
- The correspondence contains 406 proved results and 102 implemented definitions, including proof subclaims.
- The recorded axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- The three numerical suites passed all 285 recorded checks and reproduced the reference results. The comparison excludes the earlier manuscript hash and a descriptive note; all calculations, check outcomes, and numerical values are compared.

The Lean sources are byte-identical to the verified manuscript supplement. The code-only layout changes documentation and numerical output metadata.

## Records

- [Build report](../audit/build_report.json) and [build log](../audit/lean_build.log)
- [Integrated type and axiom log](../audit/lean_direct.log) and [axiom index](../audit/public_axioms.json)
- [Numerical check report](../audit/numerical_checks.json)
- [File hashes](../SHA256SUMS.csv)

Run `python scripts/verify_package.py` from the repository root to check the packaged records. To compare a new Lean run, use the commands in the [README](../README.md).
