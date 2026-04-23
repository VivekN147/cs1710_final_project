#lang forge/temporal

// basic properties to model
//  1. Durability - flushed changes survive crashes
//  2. Atomicity - either the change is made or it isn't, no half steps

// we should eventually model
//  1. Redo completeness
//  2. Undo correctness
//  3. WAL invariant

// in the future, we can model
//  1. Liveness properties - does the recovery end
//  2. Idempotency - if we do the redo process multiple times, the resulting database state shouldn't change

// Represents the smallest unit of memory in the database, equivalent to one record/row
sig Page {
    var value: one Int
}

abstract sig tState {}
one sig Active, Committed, Aborted extends tState {}

// An action done to a row, can be start/insert/update/delete/commit
sig Transaction {
    var state: one tState
}

sig Update {
    
}

// A collection of chronologically ordered transactions
sig Log {
    var logStorage: pfunc Int -> LogRecord
}

sig LogRecord {

}

// On disk memory, I/O takes time and we cannot directly edit pages, we must read them to the buffer pool
sig Disk {
    var diskStorage: set Page
}

// In cache memory, I/O is fast and this is where we are allowed to edit pages
sig Memory {
    var memoryStorage: set Page
}


// Check if the recovery process ensures durability
pred durable {
    
}

// Check if the recovery process ensures atomicity
pred atomic {
    
}
