--------------------------- MODULE MapCacheTrace ---------------------------

EXTENDS Naturals, Sequences, TLC, Trace

VARIABLE history

VARIABLE i

INSTANCE MapHistory WITH history <- history

Read == LET record == Trace[i'] IN Record(record.process, record.key, record.version)

Init ==
    /\ i = 1
    /\ history = [p \in {} |-> [k \in {} |-> <<>>]]
Next ==
    \/ i < Len(Trace) /\ i' = i + 1 /\ Read
    \/ UNCHANGED <<i, history>>

Spec == Init /\ [][Next]_<<i, history>>

=============================================================================
\* Modification History
\* Last modified Sun Feb 16 18:33:21 PST 2020 by jordanhalterman
\* Created Sun Feb 16 17:17:30 PST 2020 by jordanhalterman
