#lang forge/temporal
option run_sterling "recovery_visual.js"
option max_tracelength 15
option min_tracelength 15

// in the future, we can model
//  1. Liveness properties - does the recovery end
//  2. Idempotency - if we do the redo process multiple times, the resulting database state shouldn't change

//==========================================
// SIGS
//==========================================

// Represents the smallest unit of memory in the database, equivalent to one record
sig Page {
    var value: one Int,
    var pageLSN: one Int // LSN of the last LogRecord that modified this page
}

// Represents one transaction operation in the log
sig LogRecord {
    lsn: one Int,               // a unique Int to identify this LogRecord
    txn: one Transaction,       // which Transaction wrote this LogRecord
    page: lone Page,            // which Page is affected (none for Begin/Commit/Abort)
    recType: one RecordType,    // what kind of record
    beforeVal: lone Int,        // value before the update (for undoing)
    afterVal: lone Int,         // value after the update (for redoing)
    prevLSN: lone Int           // previous LSN for this Transaction, used to form per-Transaction chains
}

abstract sig RecordType {}
one sig Begin, Update, Commit, Abort, CLR extends RecordType {}

abstract sig TState {}
one sig Active, Committed, Aborted extends TState {}

// An action done to a record
sig Transaction {
    var tState: one TState,
    var lastLSN: lone Int // LSN of the most recent log record for this Transaction (used for undoing losers)
}

// The WAL
one sig Log {
    var records: pfunc Int -> LogRecord,    // maps LSNs to LogRecords
    var flushedLSN: one Int                 // highest LSN safely written to disk
}

// On disk memory
one sig Disk {
    var diskPages: pfunc Page -> Int,   // Page -> its durable value
    var diskLSN: pfunc Page -> Int  // Page -> lSN of last flush for that page
}

// In cache memory, I/O is fast and this is where we are allowed to edit pages
one sig Memory {
    var memPages: pfunc Page -> Int,           // Page -> its current dirty value
    var dirtyPageTable: pfunc Page -> Int   // page -> recLSN (the first LSN that dirtied it since the most recent flush)
}

// Recovery phase tracker
abstract sig Phase {}
one sig Normal, Analysis, Redo, Undo, Done extends Phase {}

one sig System {
    var phase: one Phase
}

//==========================================
// HELPERS
//==========================================

// Is a log record in the log?
pred inLog[r: LogRecord] {
    some LSN: Int | Log.records[LSN] = r
}

// LSNs are in the flushed portion of the log
pred isFlushed[LSN: Int] {
    LSN <= Log.flushedLSN
}

// A transaction is a "loser" (must be undone) if it was active at crash time
pred isLoser[t: Transaction] {
    t.tState = Active
}

// A transaction is a "winner" if it committed before crash
pred isWinner[t: Transaction] {
    t.tState = Committed
}

//==========================================
// WAL INVARIANT
//==========================================

// Before any page is written to disk, its log record must be flushed
pred walInvariant {
    all p: Page |
        some Disk.diskLSN[p] implies
            Disk.diskLSN[p] <= Log.flushedLSN
}

//==========================================
// REDO COMPLETENESS
//==========================================

// After the redo phase, every Update log record whose LSN > diskLSN[page] must have been applied
pred redoComplete {
    System.phase = Done implies {
        all r: LogRecord |
            (r.recType = Update and inLog[r]) implies {
                // If this update's LSN is after what's on disk, it must be reflected in memory
                (some p: Page | r.page = p and
                    (no Disk.diskLSN[p] or r.lsn > Disk.diskLSN[p])) implies {
                    some p: Page | r.page = p and Memory.memPages[p] = r.afterVal
                }
            }
    }
}

//==========================================
// UNDO CORRECTNESS
//==========================================

// After recovery, no effects of loser (uncommitted) transactions remain
pred undoCorrect {
    System.phase = Done implies {
        // Loser transactions: their last updates must be reversed
        all r: LogRecord |
            (r.recType = Update and inLog[r] and isLoser[r.txn]) implies {
                some p: Page | r.page = p and Memory.memPages[p] != r.afterVal
            }
        // Winner transactions: their committed updates must be present
        all r: LogRecord |
            (r.recType = Update and inLog[r] and isWinner[r.txn]) implies {
                some p: Page | r.page = p and Memory.memPages[p] = r.afterVal
            }
    }
}

//==========================================
// DURABILITY (emergent from WAL + redo)
//==========================================

// Committed transactions survive crashes: after recovery, all their updates are reflected
pred durable {
    System.phase = Done implies {
        all t: Transaction | isWinner[t] implies {
            all r: LogRecord |
                (r.txn = t and r.recType = Update and inLog[r]) implies {
                    some p: Page | r.page = p and Memory.memPages[p] = r.afterVal
                }
        }
    }
}

//==========================================
// ATOMICITY (emergent from undo)
//==========================================

// Transactions are all-or-nothing
pred atomic {
    System.phase = Done implies {
        all t: Transaction | {
            // Winner: all updates present
            (isWinner[t] implies {
                all r: LogRecord |
                    (r.txn = t and r.recType = Update and inLog[r]) implies (
                        some p: Page | r.page = p and Memory.memPages[p] = r.afterVal)
            })
            and
            // Loser: no updates present (each update is reversed)
            (isLoser[t] implies {
                all r: LogRecord |
                    (r.txn = t and r.recType = Update and inLog[r]) implies (
                        some p: Page | r.page = p and Memory.memPages[p] != r.afterVal)
            })
        }
    }
}

//==========================================
// TRANSITION PREDICATES
//==========================================

// Write a new log record during normal operation
pred writeLogRecord[r: LogRecord] {
    // Guard: normal operation, record not yet in log
    System.phase = Normal
    no Log.records[r.lsn]
    r.recType = Update

    // Log gains the new record
    Log.records' = Log.records + (r.lsn -> r)

    // flushedLSN unchanged (WAL flush is a separate step)
    Log.flushedLSN' = Log.flushedLSN

    // Buffer pool updated
    some p: Page | {
        r.page = p
        Memory.memPages' = Memory.memPages ++ (p -> r.afterVal)
        p.pageLSN' = r.lsn

        // Dirty page table: only update recLSN if page wasn't already dirty
        (no Memory.dirtyPageTable[p]) implies
            Memory.dirtyPageTable' = Memory.dirtyPageTable ++ (p -> r.lsn)
        (some Memory.dirtyPageTable[p]) implies
            Memory.dirtyPageTable' = Memory.dirtyPageTable
    }

    // Transaction's lastLSN advances
    r.txn.lastLSN' = r.lsn

    // Frame conditions
    System.phase' = Normal
    all p: Page | (r.page != p) implies {
        Memory.memPages'[p] = Memory.memPages[p]
        p.pageLSN' = p.pageLSN
        Memory.dirtyPageTable'[p] = Memory.dirtyPageTable[p]
    }
    all t: Transaction | (t != r.txn) implies t.lastLSN' = t.lastLSN
    Disk.diskPages' = Disk.diskPages
    Disk.diskLSN' = Disk.diskLSN
    all t: Transaction | t.tState' = t.tState
    all p: Page | p.value' = p.value
}

// Flush the log up to a given LSN
pred flushLog[upToLSN: Int] {
    System.phase = Normal
    upToLSN > Log.flushedLSN
    some Log.records[upToLSN]  // can only flush up to an existing record

    Log.flushedLSN' = upToLSN

    // Frame conditions
    Log.records' = Log.records
    System.phase' = Normal
    Disk.diskPages' = Disk.diskPages
    Disk.diskLSN' = Disk.diskLSN
    Memory.memPages' = Memory.memPages
    Memory.dirtyPageTable' = Memory.dirtyPageTable
    all t: Transaction | t.tState' = t.tState
    all t: Transaction | t.lastLSN' = t.lastLSN
    all p: Page | p.value' = p.value
    all p: Page | p.pageLSN' = p.pageLSN
}

// Flush a dirty page to disk
pred flushPage[p: Page] {
    System.phase = Normal
    some Memory.memPages[p]
    p.pageLSN <= Log.flushedLSN  // WAL invariant: log must be ahead of page

    Disk.diskPages' = Disk.diskPages ++ (p -> Memory.memPages[p])
    Disk.diskLSN'   = Disk.diskLSN   ++ (p -> p.pageLSN)

    // Page leaves the dirty page table once flushed
    Memory.dirtyPageTable' = Memory.dirtyPageTable - (p -> Memory.dirtyPageTable[p])

    // Frame conditions
    Log.records' = Log.records
    Log.flushedLSN' = Log.flushedLSN
    Memory.memPages' = Memory.memPages
    System.phase' = Normal
    all t: Transaction | t.tState' = t.tState
    all t: Transaction | t.lastLSN' = t.lastLSN
    all p2: Page | p2 != p implies {
        Disk.diskPages'[p2] = Disk.diskPages[p2]
        Disk.diskLSN'[p2] = Disk.diskLSN[p2]
        Memory.dirtyPageTable'[p2] = Memory.dirtyPageTable[p2]
    }
    all p2: Page | p2.value' = p2.value
    all p2: Page | p2.pageLSN' = p2.pageLSN
}

// Write a Commit record and mark it Committed
pred commitTransaction[t: Transaction, r: LogRecord] {
    System.phase = Normal
    t.tState = Active
    r.recType = Commit
    r.txn = t
    no Log.records[r.lsn]

    Log.records' = Log.records + (r.lsn -> r)
    t.tState' = Committed
    t.lastLSN' = r.lsn

    // Frame conditions
    Log.flushedLSN' = Log.flushedLSN
    System.phase' = Normal
    Disk.diskPages' = Disk.diskPages
    Disk.diskLSN' = Disk.diskLSN
    Memory.memPages' = Memory.memPages
    Memory.dirtyPageTable' = Memory.dirtyPageTable
    all t2: Transaction | t2 != t implies {
        t2.tState' = t2.tState
        t2.lastLSN' = t2.lastLSN
    }
    all p: Page | p.value' = p.value
    all p: Page | p.pageLSN' = p.pageLSN
}

// wipe memory (buffer pool is lost), leave disk and log intact
pred crash {
    System.phase = Normal

    System.phase' = Analysis

    // Buffer pool is lost
    no Memory.memPages'
    no Memory.dirtyPageTable'

    // Disk and log survive
    Log.records' = Log.records
    Log.flushedLSN' = Log.flushedLSN
    Disk.diskPages' = Disk.diskPages
    Disk.diskLSN' = Disk.diskLSN

    // Transaction states frozen as is (analysis will read them)
    all t: Transaction | t.tState' = t.tState
    all t: Transaction | t.lastLSN' = t.lastLSN
    all p: Page | p.value' = p.value
    all p: Page | p.pageLSN' = p.pageLSN
}

// Scan the log and reconstruct which transactions are winners/losers and which pages are dirty
pred runAnalysis {
    System.phase = Analysis

    System.phase' = Redo

    // Rebuild dirty page table from log
    all p: Page | {
        (some r: LogRecord | inLog[r] and r.recType = Update and r.page = p
            and (no Disk.diskLSN[p] or r.lsn > Disk.diskLSN[p]))
        implies
            Memory.dirtyPageTable'[p] =
                min[{ r: LogRecord | inLog[r] and r.recType = Update and r.page = p
                        and (no Disk.diskLSN[p] or r.lsn > Disk.diskLSN[p]) }.lsn]
        else
            no Memory.dirtyPageTable'[p]
    }

    // Mark losers (no Commit/Abort record) vs winners
    all t: Transaction | {
        (some r: LogRecord | inLog[r] and r.txn = t and r.recType = Commit)
            implies t.tState' = Committed
        else (some r: LogRecord | inLog[r] and r.txn = t and r.recType = Abort)
            implies t.tState' = Aborted
        else t.tState' = Active  // loser: was active at crash
    }

    // Frame conditions
    Log.records' = Log.records
    Log.flushedLSN' = Log.flushedLSN
    Disk.diskPages' = Disk.diskPages
    Disk.diskLSN' = Disk.diskLSN
    Memory.memPages' = Memory.memPages
    all t: Transaction | t.lastLSN' = t.lastLSN
    all p: Page | p.value' = p.value
    all p: Page | p.pageLSN' = p.pageLSN
}

// Replay every Update record in the log whose LSN > diskLSN[page]
pred runRedo {
    System.phase = Redo

    System.phase' = Undo

    // For every Update record that needs to be redone, apply afterVal
    all p: Page | {
        (some r: LogRecord | inLog[r] and r.recType = Update and r.page = p
            and (no Disk.diskLSN[p] or r.lsn > Disk.diskLSN[p]))
        implies {
            // Apply the update with the highest LSN for this page
            Memory.memPages'[p] =
                { r: LogRecord | inLog[r] and r.recType = Update and r.page = p
                    and (no Disk.diskLSN[p] or r.lsn > Disk.diskLSN[p])
                    and r.lsn = max[{ r2: LogRecord | inLog[r2] and r2.recType = Update
                        and r2.page = p }.lsn] }.afterVal
        }
        else
            Memory.memPages'[p] = Disk.diskPages[p]
    }

    // Frame conditions
    Log.records' = Log.records
    Log.flushedLSN' = Log.flushedLSN
    Disk.diskPages' = Disk.diskPages
    Disk.diskLSN' = Disk.diskLSN
    Memory.dirtyPageTable' = Memory.dirtyPageTable
    all t: Transaction | t.tState' = t.tState
    all t: Transaction | t.lastLSN' = t.lastLSN
    all p: Page | p.value' = p.value
    all p: Page | p.pageLSN' = p.pageLSN
}

// For each loser transaction, reverse its updates by applying beforeVal and writing a CLR to the log
pred runUndo {
    System.phase = Undo

    System.phase' = Done

    // For each Update record belonging to a loser, reverse it
    all p: Page | {
        (some r: LogRecord | inLog[r] and r.recType = Update and r.page = p
            and isLoser[r.txn])
        implies {
            Memory.memPages'[p] =
                { r: LogRecord | inLog[r] and r.recType = Update and r.page = p
                    and isLoser[r.txn]
                    and r.lsn = min[{ r2: LogRecord | inLog[r2] and r2.recType = Update
                        and r2.page = p and isLoser[r2.txn] }.lsn] }.beforeVal
        }
        else
            Memory.memPages'[p] = Memory.memPages[p]
    }

    // Mark losers as Aborted
    all t: Transaction | {
        isLoser[t] implies t.tState' = Aborted
        not isLoser[t] implies t.tState' = t.tState
    }

    // Frame conditions
    Log.records' = Log.records
    Log.flushedLSN' = Log.flushedLSN
    Disk.diskPages' = Disk.diskPages
    Disk.diskLSN' = Disk.diskLSN
    Memory.dirtyPageTable' = Memory.dirtyPageTable
    all t: Transaction | t.lastLSN' = t.lastLSN
    all p: Page | p.value' = p.value
    all p: Page | p.pageLSN' = p.pageLSN
}

// Stutter: once Done, stay Done
pred stutter {
    System.phase = Done
    System.phase' = Done
    Log.records' = Log.records
    Log.flushedLSN' = Log.flushedLSN
    Disk.diskPages' = Disk.diskPages
    Disk.diskLSN' = Disk.diskLSN
    Memory.memPages' = Memory.memPages
    Memory.dirtyPageTable' = Memory.dirtyPageTable
    all t: Transaction | t.tState' = t.tState
    all t: Transaction | t.lastLSN' = t.lastLSN
    all p: Page | p.value' = p.value
    all p: Page | p.pageLSN' = p.pageLSN
}

//==========================================
// ARIES-SPECIFIC STRUCTURAL PROPERTIES
//==========================================

// When a loser's update at LSN X is undone, the CLR written for it
// must point its undoNextLSN to the prevLSN of the original record,
// so the undo scan skips already-undone records
pred clrChaining {
    all clrRec: LogRecord | (inLog[clrRec] and clrRec.recType = CLR) implies {
        // The CLR's prevLSN points to the record it compensates
        some origRec: LogRecord | {
            inLog[origRec]
            origRec.recType = Update
            origRec.lsn = clrRec.prevLSN
            origRec.txn = clrRec.txn
        }
        // No other CLR in the log covers the same original record
        no clrRec2: LogRecord | {
            clrRec2 != clrRec
            inLog[clrRec2]
            clrRec2.recType = CLR
            clrRec2.prevLSN = clrRec.prevLSN
            clrRec2.txn = clrRec.txn
        }
    }
}

// The transaction table correctly identifies every transaction that committed (winner) vs was still active (loser)
pred txnTableConsistent {
    (System.phase = Redo or System.phase = Undo or System.phase = Done) implies {
        all t: Transaction | {
            // If a Commit record exists for t, it must be a winner
            (some r: LogRecord | inLog[r] and r.txn = t and r.recType = Commit)
                implies isWinner[t]
            // If no Commit record exists, it must be a loser
            (no r: LogRecord | inLog[r] and r.txn = t and r.recType = Commit)
                implies isLoser[t] or t.tState = Aborted
        }
    }
}

// The dirty page table's recLSN for a page is the first LSN that dirtied the page since its last flush
pred dirtyPageTableConsistent {
    (System.phase = Redo or System.phase = Undo or System.phase = Done) implies {
        all p: Page | some Memory.dirtyPageTable[p] implies {
            // recLSN must be <= every Update LSN for this page that is post-flush
            all r: LogRecord |
                (inLog[r] and r.recType = Update and r.page = p
                    and (no Disk.diskLSN[p] or r.lsn > Disk.diskLSN[p]))
                implies Memory.dirtyPageTable[p] <= r.lsn
        }
    }
}

// Applying the redo phase a second time produces the same memory state
pred redoIdempotent {
    System.phase = Done implies {
        all p: Page | {
            (some r: LogRecord | inLog[r] and r.recType = Update and r.page = p
                and (no Disk.diskLSN[p] or r.lsn > Disk.diskLSN[p]))
            implies {
                Memory.memPages[p] =
                    { r: LogRecord | inLog[r] and r.recType = Update and r.page = p
                        and (no Disk.diskLSN[p] or r.lsn > Disk.diskLSN[p])
                        and r.lsn = max[{ r2: LogRecord | inLog[r2] and r2.recType = Update
                            and r2.page = p }.lsn] }.afterVal
            }
        }
    }
}

//==========================================
// LIVENESS
//==========================================

// Recovery always eventually terminates: the system always reaches Done
pred recoveryTerminates {
    System.phase = Analysis implies eventually System.phase = Done
}

// The undo phase makes progress: it cannot stay in Undo forever
pred undoTerminates {
    always (System.phase = Undo implies eventually System.phase != Undo)
}

// The redo phase makes progress: it cannot stay in Redo forever
pred redoTerminates {
    always (System.phase = Redo implies eventually System.phase != Redo)
}

//==========================================
// ASSERTIONS
//==========================================

pred walAlwaysHolds {
    always (System.phase = Normal implies walInvariant)
}

pred recoveryCorrect {
    always (System.phase = Done implies (redoComplete and undoCorrect))
}

pred durabilityHolds {
    always (System.phase = Done implies durable)
}

pred atomicityHolds {
    always (System.phase = Done implies atomic)
}

pred structuralInvariants {
    always (txnTableConsistent and dirtyPageTableConsistent and clrChaining)
}

pred livenessHolds {
    recoveryTerminates and undoTerminates and redoTerminates
}

//==========================================
// INITIAL STATE
//==========================================

pred init {
    System.phase = Normal
    no Log.records
    Log.flushedLSN = 0
    no Disk.diskPages
    no Disk.diskLSN
    no Memory.memPages
    no Memory.dirtyPageTable
    all t: Transaction | t.tState = Active
    all t: Transaction | no t.lastLSN
    all p: Page | p.pageLSN = 0
}

pred finish {
    eventually { System.phase = Done }
}

//==========================================
// VALID TRACE
//==========================================

pred validTrace {
    always {
        (some r: LogRecord | writeLogRecord[r])
        or (some p: Page | flushPage[p])
        or (some upTo: Int | flushLog[upTo])
        or (some t: Transaction, r: LogRecord | commitTransaction[t, r])
        or crash
        or runAnalysis
        or runRedo
        or runUndo
        or stutter
    }
}

pred uniqueLSNs {
    all disj r1, r2: LogRecord | r1.lsn != r2.lsn
}

pred interestingTrace {
    // Force a winner by requiring a Committed transaction state during Normal phase
    // before the crash — don't reference commitTransaction directly
    some t: Transaction | {
        eventually (System.phase = Normal and t.tState = Committed)
    }

    // Force a loser — some transaction still Active when Analysis begins
    some t: Transaction | {
        eventually (System.phase = Analysis and t.tState = Active)
    }

    // Force these to be different transactions
    some disj t1, t2: Transaction | {
        eventually (System.phase = Normal and t1.tState = Committed)
        eventually (System.phase = Analysis and t2.tState = Active)
    }

    // Force update records to exist for both transactions
    some disj r1, r2: LogRecord | {
        r1.recType = Update
        r2.recType = Update
        r1.txn != r2.txn
    }

    // Force memory to be non-empty after redo
    eventually (System.phase = Undo and some Memory.memPages)
}

pred recoveryTraces {
    init
    uniqueLSNs  // add here so it always applies
    validTrace
    walAlwaysHolds
    recoveryCorrect
    durabilityHolds
    atomicityHolds
    structuralInvariants
    livenessHolds
    finish
}

run {
    recoveryTraces
    interestingTrace
} for 4 Int, exactly 2 Page, exactly 2 Transaction, exactly 6 LogRecord