# CE356 Term Project: Dijkstra's Self-Stabilization Algorithm

**Course:** CE 356: Intro to Formal Spec and Verification, Northwestern University  
**Student:** Joshua Yao  
**Semester:** Spring 2026

## Overview

Formal specification and verification of Dijkstra's self-stabilization algorithm (EWD391) using TLA+ and the TLC model checker. The algorithm guarantees that a ring of N+1 processes converges to a legitimate state (exactly one privileged process) from any arbitrary starting configuration.

## Repo Structure

- `Dijkstra.tla`: TLA+ specification of the algorithm
- `Dijkstra.toolbox/`: TLA+ Toolbox project and TLC model configuration
- `reports/`: Midterm and final reports

## TLC Verification Results (Base Spec)

- **N=3, K=4**: 256 distinct states checked, 896 states generated
- **Result:** No errors found. SelfStabilization property verified. ✅

## Planned Extension

Investigating how modifying process 0's action rule (e.g. incrementing by a different step size) affects self-stabilization, and what constraints on K are required to preserve correctness.

## Reference

Dijkstra, E.W. "Self-stabilization in spite of distributed control" (EWD391), 1973.
