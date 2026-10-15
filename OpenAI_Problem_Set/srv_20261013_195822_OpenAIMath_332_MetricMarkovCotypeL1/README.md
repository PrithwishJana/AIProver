# OpenAIMath_332_MetricMarkovCotypeL1

Problem `OpenAIMath_332_MetricMarkovCotypeL1`, run `srv_20261013_195822_OpenAIMath_332_MetricMarkovCotypeL1`.
Result: proved; the Lean proof compiles and is verified.

## Contents

- `openaimath_332_metricmarkovcotypel1_standalone.lean`: complete Lean 4 formalization and proof in one file (Mathlib)
- `openaimath_332_metricmarkovcotypel1_informal.pdf`: informalization: the theorem and every lemma with its proof, in natural language without Lean
- `openaimath_332_metricmarkovcotypel1.pdf`: report: the formalized statement and proof in mathematical language, with the Lean code
- `openaimath_332_metricmarkovcotypel1_informal.tex`: LaTeX source of the informalization
- `openaimath_332_metricmarkovcotypel1.tex`: LaTeX source of the report
- `trace.html`: walkthrough of the run, step by step (open in a browser)
- `trace_replay.html`: animated replay of the run (open in a browser)
- `lean_modules/`: Lean modules of the solution (Definitions, Theorems, Solutions, Check) and their build log
- `report_build/`: LaTeX by-products of the report and the informalization
- `run_data/`: Problem, summary and full trace of the run (JSON)
- `logs/`: Model calls and the orchestrator log

## Models

- orchestrator: Opus 5.5 (high reasoning)
- auditor: Sonnet 5.5
- reviewer: Opus 5.5 (high reasoning)
- writer: Opus 5.5 (high reasoning)
- subagent: AIProver trained (FP8, Vista)

The standalone file compiles with Lean v4.23.0 and Mathlib v4.23.0 in a Lake project:
`lake env lean <file>`.
