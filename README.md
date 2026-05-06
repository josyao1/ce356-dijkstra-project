# CE356 Dijkstra Self-Stabilization Project

**GitHub:** https://github.com/josyao1/ce356-dijkstra-project

Formal verification of Dijkstra's self-stabilizing token ring algorithm using TLA+.

## Overview

This project models and verifies Dijkstra's classic self-stabilization algorithm, where a ring of N+1 processes eventually reaches a legitimate state (exactly one privileged process) regardless of the initial state.

## Files

- `Dijkstra.tla` — TLA+ specification of the algorithm
- `Dijkstra.toolbox/` — TLC model checker configuration and model snapshots
- `reports/` — Midterm progress report

## Running the Model

Open `Dijkstra.tla` in the [TLA+ Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html) and run `Model_1` with the TLC model checker. Configure constants `N` (number of non-root processes) and `K` (number of token values, must satisfy K > N).

## Key Properties

- **Legitimacy:** `Legitimate` — exactly one process is privileged
- **Self-stabilization:** Starting from any state, the system eventually reaches a legitimate state (verified via `FairSpec` and liveness properties)
