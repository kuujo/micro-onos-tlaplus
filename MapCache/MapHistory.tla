----------------------------- MODULE MapHistory -----------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The history of history for the client, used by the model checker to verify sequential consistency
VARIABLE history

\* The type invariant checks that the client's history never go back in time
TypeInvariant ==
    /\ \A c \in DOMAIN history :
       /\ \A k \in DOMAIN history[c] :
          /\ \A r \in DOMAIN history[c][k] :
                r > 1 => history[c][k][r] >= history[c][k][r-1]

\* Record a read to the history
Record(c, k, v) ==
    /\ \/ /\ c \in DOMAIN history
          /\ k \in DOMAIN history[c]
          /\ history' = [history EXCEPT ![c][k] = Append(history[c][k], v)]
       \/ /\ c \in DOMAIN history
          /\ k \notin DOMAIN history[c]
          /\ history' = [history EXCEPT ![c] = history[c] @@ (k :> <<v>>)]
       \/ /\ c \notin DOMAIN history
          /\ history' = history @@ (c :> [i \in {k} |-> <<v>>])

=============================================================================
\* Modification History
\* Last modified Sun Feb 16 18:44:34 PST 2020 by jordanhalterman
\* Created Sun Feb 16 17:52:57 PST 2020 by jordanhalterman
