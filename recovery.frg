#lang forge/temporal

// basic properties to model
//  1. Redo completeness
//  2. Undo correctness
//  3. WAL invariant

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
one sig Normal, Crashed, Analysis, Redo, Undo, Done extends Phase {}

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
// ASSERTIONS
//==========================================

// WAL must hold in every state during normal operation
pred walAlwaysHolds {
    always (System.phase = Normal implies walInvariant)
}

// After full recovery: redo is complete, undo is correct
pred recoveryCorrect {
    always (System.phase = Done implies (redoComplete and undoCorrect))
}

// Durability and atomicity hold after recovery (emergent consequences)
pred durabilityHolds {
    always (System.phase = Done implies durable)
}

pred atomicityHolds {
    always (System.phase = Done implies atomic)
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
    eventually {System.phase = Done}
}

pred recoveryTraces {
    // TODO: Fill me in!
    // Start in the initial state
    init

    walAlwaysHolds
    recoveryCorrect
    durabilityHolds
    atomicityHolds

    finish
}

//==========================================
// RUN
//==========================================

run { recoveryTraces } for 3 Int, exactly 2 Page, exactly 2 Transaction, exactly 4 LogRecord