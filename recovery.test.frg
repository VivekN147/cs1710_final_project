#lang forge/temporal

open "recovery.frg"

//==========================================
// TESTS: init
//==========================================

test suite for init {
    test expect {
        -- init is satisfiable
        initIsSat: {
            init
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- init starts in Normal phase
        initIsNormal: {
            init and System.phase != Normal
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- init has no log records
        initHasNoLog: {
            init and some Log.records
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- init has no disk pages
        initHasNoDisk: {
            init and some Disk.diskPages
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- init has no memory pages
        initHasNoMemory: {
            init and some Memory.memPages
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- init has flushedLSN of 0
        initFlushedLSNIsZero: {
            init and Log.flushedLSN != 0
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- all transactions start Active
        initAllActive: {
            init and (some t: Transaction | t.tState != Active)
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- all pages start with pageLSN 0
        initPageLSNZero: {
            init and (some p: Page | p.pageLSN != 0)
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat
    }
}

//==========================================
// TESTS: walInvariant
//==========================================

test suite for walInvariant {
    test expect {
        -- WAL holds when disk is empty
        walHoldsWhenNoDisk: {
            no Disk.diskLSN
            walInvariant
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- WAL holds when diskLSN <= flushedLSN
        walHoldsWhenFlushed: {
            some p: Page | {
                Disk.diskLSN[p] = 1
                Log.flushedLSN = 2
            }
            walInvariant
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- WAL is violated when diskLSN > flushedLSN
        walViolatedWhenAhead: {
            some p: Page | {
                Disk.diskLSN[p] = 3
                Log.flushedLSN = 2
            }
            walInvariant
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- WAL holds when diskLSN = flushedLSN
        walHoldsWhenEqual: {
            some p: Page | {
                Disk.diskLSN[p] = 2
                Log.flushedLSN = 2
            }
            walInvariant
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat
    }
}

//==========================================
// TESTS: isWinner / isLoser
//==========================================

test suite for isWinner {
    test expect {
        -- Committed transaction is a winner
        committedIsWinner: {
            some t: Transaction | {
                t.tState = Committed
                isWinner[t]
            }
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- Active transaction is not a winner
        activeIsNotWinner: {
            some t: Transaction | {
                t.tState = Active
                isWinner[t]
            }
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- Aborted transaction is not a winner
        abortedIsNotWinner: {
            some t: Transaction | {
                t.tState = Aborted
                isWinner[t]
            }
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat
    }
}

test suite for isLoser {
    test expect {
        -- Active transaction is a loser
        activeIsLoser: {
            some t: Transaction | {
                t.tState = Active
                isLoser[t]
            }
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- Committed transaction is not a loser
        committedIsNotLoser: {
            some t: Transaction | {
                t.tState = Committed
                isLoser[t]
            }
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- A transaction cannot be both winner and loser
        notBothWinnerAndLoser: {
            some t: Transaction | isWinner[t] and isLoser[t]
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat
    }
}

//==========================================
// TESTS: crash
//==========================================

test suite for crash {
    test expect {
        -- crash is satisfiable from Normal
        crashIsSat: {
            System.phase = Normal
            crash
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- crash cannot happen outside Normal
        crashRequiresNormal: {
            System.phase = Redo
            crash
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- after crash, phase is Analysis
        crashLeadsToAnalysis: {
            System.phase = Normal
            crash
            System.phase' != Analysis
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- after crash, memory is wiped
        crashWipesMemory: {
            System.phase = Normal
            some Memory.memPages
            crash
            some Memory.memPages'
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- after crash, log is preserved
        crashPreservesLog: {
            System.phase = Normal
            crash
            Log.records' != Log.records
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- after crash, disk is preserved
        crashPreservesDisk: {
            System.phase = Normal
            crash
            Disk.diskPages' != Disk.diskPages
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat
    }
}

//==========================================
// TESTS: runAnalysis
//==========================================

test suite for runAnalysis {
    test expect {
        -- runAnalysis is satisfiable from Analysis phase
        analysisIsSat: {
            System.phase = Analysis
            runAnalysis
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- runAnalysis cannot run outside Analysis phase
        analysisRequiresAnalysisPhase: {
            System.phase = Normal
            runAnalysis
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- after analysis, phase is Redo
        analysisLeadsToRedo: {
            System.phase = Analysis
            runAnalysis
            System.phase' != Redo
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- after analysis, a transaction with a Commit record becomes a winner
        analysisMarksWinners: {
            System.phase = Analysis
            some t: Transaction, r: LogRecord | {
                r.txn = t
                r.recType = Commit
                inLog[r]
                runAnalysis
                t.tState' != Committed
            }
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- after analysis, a transaction with no Commit record is a loser
        analysisMarksLosers: {
            System.phase = Analysis
            some t: Transaction | {
                no r: LogRecord | inLog[r] and r.txn = t and r.recType = Commit
                runAnalysis
                t.tState' = Committed
            }
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat
    }
}

//==========================================
// TESTS: runRedo
//==========================================

test suite for runRedo {
    test expect {
        -- runRedo is satisfiable from Redo phase
        redoIsSat: {
            System.phase = Redo
            runRedo
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- runRedo cannot run outside Redo phase
        redoRequiresRedoPhase: {
            System.phase = Normal
            runRedo
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- after redo, phase is Undo
        redoLeadsToUndo: {
            System.phase = Redo
            runRedo
            System.phase' != Undo
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- after redo, disk is unchanged
        redoLeavesDiskAlone: {
            System.phase = Redo
            runRedo
            Disk.diskPages' != Disk.diskPages
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- after redo, log is unchanged
        redoLeavesLogAlone: {
            System.phase = Redo
            runRedo
            Log.records' != Log.records
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat
    }
}

//==========================================
// TESTS: runUndo
//==========================================

test suite for runUndo {
    test expect {
        -- runUndo is satisfiable from Undo phase
        undoIsSat: {
            System.phase = Undo
            runUndo
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- runUndo cannot run outside Undo phase
        undoRequiresUndoPhase: {
            System.phase = Normal
            runUndo
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- after undo, phase is Done
        undoLeadsToDone: {
            System.phase = Undo
            runUndo
            System.phase' != Done
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- after undo, losers are marked Aborted
        undoAbortsLosers: {
            System.phase = Undo
            some t: Transaction | {
                isLoser[t]
                runUndo
                t.tState' != Aborted
            }
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- after undo, winners remain Committed
        undoPreservesWinners: {
            System.phase = Undo
            some t: Transaction | {
                isWinner[t]
                runUndo
                t.tState' != Committed
            }
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- after undo, disk is unchanged
        undoLeavesDiskAlone: {
            System.phase = Undo
            runUndo
            Disk.diskPages' != Disk.diskPages
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat
    }
}

//==========================================
// TESTS: stutter
//==========================================

test suite for stutter {
    test expect {
        -- stutter is satisfiable in Done
        stutterIsSat: {
            System.phase = Done
            stutter
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- stutter cannot occur outside Done
        stutterRequiresDone: {
            System.phase = Normal
            stutter
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- stutter preserves phase
        stutterKeepsDone: {
            System.phase = Done
            stutter
            System.phase' != Done
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- stutter preserves memory
        stutterPreservesMemory: {
            System.phase = Done
            stutter
            Memory.memPages' != Memory.memPages
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- stutter preserves log
        stutterPreservesLog: {
            System.phase = Done
            stutter
            Log.records' != Log.records
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat
    }
}

//==========================================
// TESTS: txnTableConsistent
//==========================================

test suite for txnTableConsistent {
    test expect {
        -- txnTableConsistent holds trivially when log is empty
        consistentWithEmptyLog: {
            System.phase = Redo
            no Log.records
            txnTableConsistent
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- a committed transaction with a Commit record is consistent
        consistentWhenCommitRecordExists: {
            System.phase = Redo
            some t: Transaction, r: LogRecord | {
                t.tState = Committed
                r.txn = t
                r.recType = Commit
                inLog[r]
            }
            txnTableConsistent
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- marking a transaction Committed with no Commit record violates consistency
        inconsistentWhenCommitRecordButNotCommitted: {
            System.phase = Redo
            some t: Transaction, r: LogRecord | {
                t.tState = Active
                r.txn = t
                r.recType = Commit
                inLog[r]
                txnTableConsistent
            }
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat
    }
}

//==========================================
// TESTS: dirtyPageTableConsistent
//==========================================

test suite for dirtyPageTableConsistent {
    test expect {
        -- consistent when dirty page table is empty
        dptConsistentWhenEmpty: {
            System.phase = Redo
            no Memory.dirtyPageTable
            dirtyPageTableConsistent
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- recLSN <= all update LSNs for that page is consistent
        dptConsistentWhenRecLSNIsMin: {
            System.phase = Redo
            some p: Page, r: LogRecord | {
                r.recType = Update
                r.page = p
                r.lsn = 2
                inLog[r]
                no Disk.diskLSN[p]
                Memory.dirtyPageTable[p] = 1
            }
            dirtyPageTableConsistent
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- recLSN > an update LSN for that page violates consistency
        dptInconsistentWhenRecLSNTooHigh: {
            System.phase = Redo
            some p: Page, r: LogRecord | {
                r.recType = Update
                r.page = p
                r.lsn = 1
                inLog[r]
                no Disk.diskLSN[p]
                Memory.dirtyPageTable[p] = 3
                no r2: LogRecord | r2 != r and inLog[r2] and r2.recType = Update and r2.page = p
            }
            dirtyPageTableConsistent
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat
    }
}

//==========================================
// TESTS: clrChaining
//==========================================

test suite for clrChaining {
    test expect {
        -- clrChaining holds when there are no CLRs
        chainingHoldsWithNoCLRs: {
            no r: LogRecord | inLog[r] and r.recType = CLR
            clrChaining
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- a CLR pointing to a valid Update record satisfies chaining
        chainingHoldsWithValidCLR: {
            some disj origRec, clrRec: LogRecord, t: Transaction | {
                origRec.recType = Update
                origRec.lsn = 1
                origRec.txn = t
                inLog[origRec]
                clrRec.recType = CLR
                clrRec.prevLSN = 1
                clrRec.txn = t
                inLog[clrRec]
            }
            clrChaining
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- two CLRs compensating the same record violates chaining
        chainingViolatedByDuplicateCLR: {
            some disj origRec, clrRec1, clrRec2: LogRecord, t: Transaction | {
                origRec.recType = Update
                origRec.lsn = 1
                origRec.txn = t
                inLog[origRec]
                clrRec1.recType = CLR
                clrRec1.prevLSN = 1
                clrRec1.txn = t
                inLog[clrRec1]
                clrRec2.recType = CLR
                clrRec2.prevLSN = 1
                clrRec2.txn = t
                inLog[clrRec2]
            }
            clrChaining
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat
    }
}

//==========================================
// TESTS: redoIdempotent
//==========================================

test suite for redoIdempotent {
    test expect {
        -- idempotency holds trivially when system is not Done
        idempotentTriviallyHolds: {
            System.phase = Normal
            redoIdempotent
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- idempotency holds when no update records exist
        idempotentWithNoUpdates: {
            System.phase = Done
            no r: LogRecord | inLog[r] and r.recType = Update
            redoIdempotent
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat
    }
}

//==========================================
// TESTS: recoveryTraces (end-to-end)
//==========================================

test suite for recoveryTraces {
    test expect {
        -- a valid recovery trace exists
        traceExists: {
            recoveryTraces
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- every recovery trace starts in Normal
        tracesStartInNormal: {
            recoveryTraces and System.phase != Normal
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- every recovery trace eventually reaches Done
        tracesReachDone: {
            recoveryTraces
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is sat

        -- WAL invariant is never violated during Normal operation
        walNeverViolatedInNormal: {
            recoveryTraces
            eventually (System.phase = Normal and not walInvariant)
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- the system cannot go from Done back to Normal
        doneIsTerminal: {
            recoveryTraces
            eventually (System.phase = Done and System.phase' = Normal)
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- the system cannot skip directly from Normal to Redo
        cannotSkipAnalysis: {
            recoveryTraces
            eventually (System.phase = Normal and System.phase' = Redo)
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat

        -- the system cannot go from Analysis back to Normal
        analysisIsOneWay: {
            recoveryTraces
            eventually (System.phase = Analysis and System.phase' = Normal)
        } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord is unsat
    }
}
