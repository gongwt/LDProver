# LDProver — C++20 Go Life-and-Death Prover & Verification Workbench

LDProver is a high-performance C++20 Go life-and-death (tsumego) solver and zero-trust proof verifier, paired with a modern TypeScript/React/Vite interactive verification workbench.

## Architecture Overview

- **C++20 Native Prover & Zero-Trust Verifier (`cpp/`, `tprover` CLI)**:
  - Implements `1+ε` AND/OR Df-Pn search.
  - Classic Benson (1976) unconditional status (UCA) terminal evaluation.
  - SSK/PSK full-BitBoard `HistorySet` superko detection.
  - Relevance Zone (`OutsideRZ`) pruning and dynamic pruning.
  - BoardTT + 4-branch Radix-Tree PatternTT for high-speed transposition lookups.
- **TypeScript/React/Vite Verification Workbench (`src/`)**:
  - Interactive board representation, search visualization, and proof inspection.

## Repository Layout

- `cpp/`: Core C++20 library, solver engines, and tests (`ldprover_r5_tests`, `ldprover_cli_tests`).
- `src/`: React frontend workbench and TypeScript utilities.
- `public/tsumego/`: Benchmark and problem JSON datasets (e.g., `chao_vol1_p042.json`).
- `scripts/verify_r5_regression.ts`: Automated R5 regression verification suite.
- Root & collaboration documentation / review reports:
  - `AGENTS.md`
  - `docs/agent-task-template.md`
  - `HARD_TSUMEGO_PERFORMANCE_ROADMAP_2026-11-22.md`
  - `DEVELOPMENT_RECOMMENDATIONS_2026-11-22.md`
  - `REVIEW_EVIDENCE_2026-11-23.json`
  - `INDEPENDENT_FAILURE_REVIEW_*.md`
  - `P090_SEARCH_TRACE_2026-11-21.md`
  - `SOLVER_FAILURE_ANALYSIS_2026-11-21.md`

## C++20 Build, Test & CLI Commands

- **Build**:
  ```bash
  cmake -S cpp -B build -DCMAKE_BUILD_TYPE=Release && cmake --build build -j
  ```
- **Test**:
  ```bash
  ctest --test-dir build --output-on-failure --verbose
  ```
  *(Runs `ldprover_r5_tests` 302/302 and POSIX `ldprover_cli_tests` 18/18)*
- **Solve**:
  ```bash
  ./build/tprover solve --problem public/tsumego/chao_vol1_p042.json --node-limit 3500 --out-proof /tmp/p042.proof.json
  ```
  *(Optional flags: `--profile-json <file>`, `--convergence-json <file> --observe-paths <csv>`, `--near-pn-continuation` [default OFF])*
- **Check Proof**:
  ```bash
  ./build/tprover check --problem public/tsumego/chao_vol1_p042.json --proof /tmp/p042.proof.json
  ```
- **Benchmark**:
  ```bash
  ./build/tprover bench --manifest <manifest.txt> --out /tmp/bench.csv
  ```

## Web Workbench & TypeScript Commands

- **Development Server**:
  ```bash
  npm install && npm run dev
  ```
  *(Accessible at `http://localhost:3000`)*
- **Production Build & Lint**:
  ```bash
  npm run build && npm run lint
  ```
- **Regression Verification**:
  ```bash
  npx --no-install tsx scripts/verify_r5_regression.ts
  ```
  *(Verifies 274/274 assertions)*

## Current Verified Status through R29

- **Default Baseline**: Arm D remains the default C++20 baseline (reusable legal-move scratch buffers, incremental Zobrist hashing, precomputed orthogonal neighbor tables `kOrthoNeighbors<N>`, and atomic/Unicode-safe CLI output). 4/4 default SHA-256 invariance is verified against `0a1abb6` (`p031`/`p042` `PASS`, `p060`/`p090` `LP-U01` under `original_root`).
- **R27–R29 Additions**:
  - `solve_root_relative` convergence observer path alignment and non-terminal subproof separation.
  - Read-only zero-trust `VerifySubproofAtPath` and `VerifySiblingQueryReplay` APIs with `SubproofBindingPolicy` (`kStrictWhenRootProven`, `kRequireBoundRootEdge`, `kSemanticReplayOnly`), separate source/query provenance fields (`source_edge_binding_status`, `source_edge_bound_to_root_dag`, `source_recorded_edge_dag_node_id`), and structural prefix pre-checks before indexing.
  - Opt-in `--near-pn-continuation` (default OFF, with zero-budget disabled semantics; R27 continuation study concluded per stopping criteria).
