--------------------------- MODULE MapCacheTrace ---------------------------

EXTENDS Naturals, Sequences, TLC, Trace

VARIABLE reads

VARIABLE events

VARIABLE i

INSTANCE MapHistory WITH history <- reads, events <- events

Read == 
    LET record == Trace[i'] 
    IN 
       \/ /\ \/ record.op = "put"
             \/ record.op = "get"
             \/ record.op = "remove"
          /\ RecordRead(record.process, record.key, record.version)
          /\ UNCHANGED <<events>>
       \/ /\ record.op = "event"
          /\ RecordEvent(record.process, record.key, record.version)
          /\ UNCHANGED <<reads>>

Init ==
    /\ i = 0
    /\ reads = [p \in {} |-> [k \in {} |-> <<>>]]
    /\ events = [p \in {} |-> [k \in {} |-> <<>>]]
Next ==
    \/ i < Len(Trace) /\ i' = i + 1 /\ Read
    \/ UNCHANGED <<i, reads, events>>

Spec == Init /\ [][Next]_<<i, reads, events>>

=============================================================================
\* Modification History
\* Last modified Sun Feb 16 20:13:57 PST 2020 by jordanhalterman
\* Created Sun Feb 16 17:17:30 PST 2020 by jordanhalterman
