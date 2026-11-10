# Brute-force example entry

A deliberately simple solver that tries every assignment and checks every clause. It exists to test the competition pipeline end to end. It is not meant to compete.

`design.py` is the template's register-map shell, unchanged (a test checks the two are identical). `solver.py` is the only file that differs from the template.

## What it does

- Stores the clause stream (literals, with a 0 after each clause) in a 256-word memory.
- On start, walks all `2**nvars` assignments. For each one it scans the clauses until one is unsatisfied. If none is, the answer is SAT and the assignment is the model. After the last assignment it answers UNSAT.
- Declared capacity: 12 variables, 64 clauses, 192 literals. Larger instances are skipped by the runner and count as unsolved.

Worst case is about `2**nvars * (nlits + nclauses)` cycles, so it is only usable on tiny formulas.

## Measured

| | |
|---|---|
| Yosys `synth_ecp5` | 446 LUT4, 186 FF, 64 distributed-RAM blocks (`TRELLIS_DPR16X4`), 115 carry cells, no block RAM or DSP |
| nextpnr `TRELLIS_COMB` (what the platform's "logic" count uses) | 1,110 |
| Standalone nextpnr, 50 MHz target | 78.9 MHz, passes |

The standalone place-and-route is the design alone, with local tools (Yosys 0.62, nextpnr 0.9) and not the pinned versions or the full SoC, so it is indicative only. Nothing here has run on a board.

## Tests

`backend/tests/test_bruteforce_rtl.py` drives the simulated RTL with the real runner, pre-flight and campaign:

```sh
cd backend && pytest tests/test_bruteforce_rtl.py
```

It passes pre-flight, solves random small instances correctly, handles the edge cases (empty formula, empty clause, zero variables, a model that is only found at the last assignment), skips over-capacity instances, and is aborted at the time limit and reused afterwards.
