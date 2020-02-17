----------------------------- MODULE MapHistory -----------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The history of history for the client, used by the model checker to verify sequential consistency
VARIABLE history

\* The history of events received by the client, used by the model checker to verify sequential consistency
VARIABLE events

\* The state invariant checks that the client's history never go back in time
StateInvariant ==
    /\ \A c \in DOMAIN history :
       /\ \A k \in DOMAIN history[c] :
          /\ \A r \in DOMAIN history[c][k] :
                r > 1 => history[c][k][r] >= history[c][k][r-1]

\* The events invariant checks that events are sequential
EventInvariant ==
    /\ \A c \in DOMAIN events :
       /\ \A k \in DOMAIN events[c] :
          /\ \A r \in DOMAIN events[c][k] :
                r > 1 => events[c][k][r] > events[c][k][r-1]

\* Record a read to the history
RecordRead(c, k, v) ==
    /\ \/ /\ c \in DOMAIN history
          /\ k \in DOMAIN history[c]
          /\ history' = [history EXCEPT ![c][k] = Append(history[c][k], v)]
       \/ /\ c \in DOMAIN history
          /\ k \notin DOMAIN history[c]
          /\ history' = [history EXCEPT ![c] = history[c] @@ (k :> <<v>>)]
       \/ /\ c \notin DOMAIN history
          /\ history' = history @@ (c :> [i \in {k} |-> <<v>>])

\* Record an event to the history
RecordEvent(c, k, v) ==
    /\ \/ /\ c \in DOMAIN events
          /\ k \in DOMAIN events[c]
          /\ events' = [events EXCEPT ![c][k] = Append(events[c][k], v)]
       \/ /\ c \in DOMAIN events
          /\ k \notin DOMAIN events[c]
          /\ events' = [events EXCEPT ![c] = events[c] @@ (k :> <<v>>)]
       \/ /\ c \notin DOMAIN events
          /\ events' = events @@ (c :> [i \in {k} |-> <<v>>])

=============================================================================
\* Modification History
\* Last modified Sun Feb 16 19:11:53 PST 2020 by jordanhalterman
\* Created Sun Feb 16 17:52:57 PST 2020 by jordanhalterman
