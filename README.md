# Commodity classification for policy evaluation

Lean proofs and supplementary numerical checks for **Commodity Classification for Policy Evaluation in General Equilibrium**, by Hideyasu Sato, Toyo University.

The paper studies which products can share an input report while preserving general-equilibrium welfare evaluation for a fixed tax policy. It derives exact classification conditions and precision bounds for coarse reports.

All mathematical results, equilibrium constructions, and examples in the main text and mathematical appendices are formalized and verified in Lean 4. The [correspondence guide](docs/correspondence.md) connects the paper to the code. The full index contains 508 correspondence units: 406 proved results and 102 definitions. These units include proof subclaims.

## Contents

```text
LeanMath/CommodityClassification/   Lean definitions, proofs, and audits
docs/                              Paper correspondence and validation guide
audit/                             Lean build and axiom records
numerical/                         Supplementary symbolic and numerical checks
reference_results/                 Recorded numerical outputs
scripts/verify_package.py          File and correspondence checks
SHA256SUMS.csv                     Release file hashes
```

## Verify the Lean proofs

Use Lean **4.35.0** and the supplied `lake-manifest.json`, which pins Mathlib to `56a005855ea17e0b0958f73ec801ae140b0a1679`. From the repository root, with Lean/Lake installed:

```sh
lake exe cache get
lake build LeanMath LeanMath.CommodityClassification.CheckAllManuscript
lake env lean LeanMath/CommodityClassification/CheckAllManuscript.lean > lean-audit.log
python scripts/verify_package.py --lean-log lean-audit.log
```

The first command downloads dependency caches. The final command checks file hashes, correspondence, and the exact declaration types and axioms printed by Lean. It can also run without `--lean-log` to check the packaged records.

## Run the numerical checks

Tested with Python **3.12** and SymPy **1.14.0**:

```sh
python -m pip install -r numerical/requirements.txt
python numerical/run_all.py
```

The three suites run 285 recorded checks and compare their results with `reference_results/`. Generated outputs go to `numerical/notes/`.

## Find a result

- [Main results and their Lean entry points](docs/correspondence.md)
- [Complete correspondence table](docs/correspondence.csv)
- [Validation record](docs/validation.md)

For a searchable index, download the repository and open `docs/index.html` in a browser. `docs/claims.json` records claim dependencies and scope; `docs/declarations.json` records declaration types, source locations, and axioms. The [manuscript version record](docs/manuscript_version.json) identifies the paper edition used for the correspondence.

## Citation, funding, and license

**Archived release v0.1.0:** [DOI: 10.5281/zenodo.23637155](https://doi.org/10.5281/zenodo.23637155).

Author and software citation metadata are in [CITATION.cff](CITATION.cff). The associated paper is *Commodity Classification for Policy Evaluation in General Equilibrium* (2026).

Supported by JSPS KAKENHI Grant Number **JP23K25496**.

Code and accompanying documentation are distributed under the [MIT license](LICENSE).
