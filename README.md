# Fundamental Theorem of Discrete Asset Pricing — Lean formalization

Lean 4 formalization accompanying **Fundamental Theorem of Discrete Asset Pricing** by Masaaki Fukasawa.

The paper studies prices that take values in a locally finite subset of a finite-dimensional space while time is continuous. Under the stated path regularity and local boundedness assumptions, ordinary no arbitrage suffices for the fundamental theorem:

**NA ⇔ NFLVR ⇔ NFL ⇔ existence of an equivalent local martingale probability measure.**

The formalization also proves weak-star closedness of the admissible trading cone under NA and the existence of an equivalent true martingale measure when prices are bounded. Trading gains are finite sums over the jumps of each path.

## Reproduce the verification

Install [elan](https://github.com/leanprover/elan#installation), Git, and Python 3.9 or newer, then run:

```sh
git clone https://github.com/MasaakiFukasawa/ftdap-lean.git
cd ftdap-lean
lake exe cache get
python3 scripts/verify.py
```

The toolchain is **Lean 4.34.0**. Mathlib is pinned to commit `5ed2965256430c3649e86755f9576b54eca72435`, and `lake-manifest.json` fixes the transitive dependencies. The first run downloads the toolchain and dependencies and requires several gigabytes of disk space. It does not require the author's local projects.

For compilation alone, use `lake build`. For the build plus axiom audit, use `scripts/verify.py` as above. To rebuild the project proofs from scratch, run `lake clean` before verification.

The verifier:

- checks that all **127 source modules** are included in the build;
- rejects proof placeholders and explicit additional axioms in the project sources;
- compiles with warnings treated as errors;
- checks the transitive axiom dependencies of **323 declarations**, allowing only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

Successful verification writes `verification.json`, including hashes of all proof sources. Detailed output is in `build.log` and `verification.log`. The GitHub Actions workflow runs the same commands and retains these files as run artifacts. Generated Lean objects and dependency caches are excluded from the repository.

## Where to start

| File | Content |
| --- | --- |
| [CompactSourceFTAP.lean](src/CompactSourceFTAP.lean) | Main theorem `FTDAP.compact_horizon_ftap` and bounded-price theorem `FTDAP.compact_horizon_bounded_ftap`, starting from prices on `[0,T]` |
| [SourceFTAP.lean](src/SourceFTAP.lean) | Full equivalences for real-indexed source prices, allowing exceptional paths on a null set |
| [Geometry.lean](src/Geometry.lean), [FiniteSelection.lean](src/FiniteSelection.lean) | Finite-dimensional geometry and portfolio reduction |
| [TradingConeClosed.lean](src/TradingConeClosed.lean) | Weak-star closedness of the actual admissible trading cone |
| [ForwardFTAP.lean](src/ForwardFTAP.lean) | Construction of an equivalent local martingale measure under NA |
| [ConverseFTAP.lean](src/ConverseFTAP.lean) | Direct converse: an equivalent local martingale measure implies NA |
| [KreinSmulian.lean](src/KreinSmulian.lean) | Krein–Šmulian theorem used in the closedness proof |
| [AllChecks.lean](src/AllChecks.lean) | Axiom audit of the main declarations |

[AUDIT.txt](AUDIT.txt) maps the remaining proof modules to the mathematical argument. The source files keep the flat module names used during formalization; declarations are generally in the namespace `FTDAP`.

## Exact scope

The final theorem assumes a probability space, a right-continuous filtration containing all ambient null sets, and a finite-dimensional real inner product price space. Prices are adapted, have almost surely càdlàg paths, start at a deterministic value, and stay in a locally finite state set. Local boundedness is expressed by increasing stopping times, eventually equal to the finite horizon almost surely, with deterministic bounds on stopped prices.

From these assumptions Lean constructs the measurable finite-jump representation. Admissible holdings are arbitrary predictable vector-valued processes with a deterministic lower bound on wealth; bounded or integrable holdings are not required. `HorizonLocalMartingale` expresses the local martingale property on the closed horizon using mathlib martingales and explicit stopping times. NFL and NFLVR use the actual weak-star and norm closures, respectively.

Lean checks the formal statements and their proofs. The correspondence between these definitions and the manuscript is documented in the audit; the manuscript itself is not included in this repository.

## Acknowledgments and AI use

This work was supported by JSPS KAKENHI Grant Number **25K07112**. OpenAI Codex assisted in developing, checking, and packaging the formalization. Mathematical statements and their interpretation remain the author's responsibility; successful kernel checking applies to the Lean statements.

Mathlib-derived files retain their copyright headers. See [PINNED_MODULES.txt](PINNED_MODULES.txt) and [NOTICE](NOTICE) for source provenance and modifications.

## License

A license for the original code and documentation has not yet been selected. The third-party material identified in [NOTICE](NOTICE) retains its Apache 2.0 terms; see [LICENSE](LICENSE) for the scope and [LICENSES/Apache-2.0.txt](LICENSES/Apache-2.0.txt) for the full text.
