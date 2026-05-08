# ARIES Recovery

Our model simulates ARIES recovery in forge. We wanted to formally verify that you can fully recover a database safely using WAL, undo, and redo

## Scope
- Core: pages, log records, LSNs, transaction states, WAL, memory and disk values, phases of recovery, redo completeness / undo correctness, and durability and atomicity
- Closely related: analysis, CLRs, prevLSN, before and after vals, and the dirty page table. We abstracted out a lot because a full database would be nearly impossible to model in forge
- Out of scope: Schemas, locks, checkpoints, real disk behavior. We also only used integers for the values on our pages because different data types aren't particularly relevant to recovery

## How does it work?

- In the normal state, records can be updated, log records and dirty pages can be flushed, and transactions can be committed.
- Analysis rebuilds information around transactions and dirty pages using just the log, and redo applies the logged updates that are newer than the last LSN, then undo reverses any uncommitted transactions and also marks them as aborted

## Properties checked

- walInvariant: disk pages can't be ahead of the flushed log
- The model checks redo completeness, undo correctness, durability, atomicity, and progress of the recovery

## Visualization

- Our visualizer visualizes phases, the states of transactions, memory and disk, the WAL, and flushed LSN
- Step through the temporal instance and look at the visualizer to see database functioning in the normal state, recovering from a crash, redoing, undoing, and reaching the end of recovery

## Takeaways

- The WAL prevents the disk from ever getting ahead of the log
- Redo always persists committed transactions and undo never persists uncommitted transactions
- The model clearly captures the structure of recovery, but abstracts away a lot of the smaller details with a real ARIES implementation, like checkpoints and real storage behavior

## Running

- Run recovery.frg and look at the demo examples
- Step through the temporal states and view them in the visualizer