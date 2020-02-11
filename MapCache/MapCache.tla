------------------------------ MODULE MapCache ------------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* An empty value
CONSTANT Nil

\* The set of clients
CONSTANT Client

\* The set of possible keys
CONSTANT Key

\* The set of possible values
CONSTANT Value

\* The system state
VARIABLE state

\* The cache state
VARIABLE cache

\* A bag of pending cache entries
VARIABLE pending

\* A sequence of update events
VARIABLE events

\* The maximum version assigned to an event
VARIABLE version

\* The history of reads for the client; used by the model checker to verify sequential consistency
VARIABLE reads

vars == <<state, cache, events, version, reads>>

----

\* The type invariant checks that the client's reads never go back in time
TypeInvariant ==
    /\ \A c \in Client :
       /\ \A k \in Key :
          /\ \A r \in DOMAIN reads[c][k] :
                r > 1 => reads[c][k][r] >= reads[c][k][r-1]

----

(*
This section models helpers for managing the system and cache state
*)

\* Drop a key from the domain of a function
DropKey(s, k) == [i \in DOMAIN s \ {k} |-> s[i]]

\* Put an entry in the given function
PutEntry(s, e) == 
    IF e.key \in DOMAIN s THEN
        [s EXCEPT ![e.key] = e]
    ELSE
        s @@ (e.key :> e)

----

(*
This section models the method calls for the Map primitive.
Map entries can be created, updated, deleted, and read. When the map state is changed,
events are enqueued for the client, and the learner updates the cache.
*)

\* Get a value/version for a key in the map
Get(c, k) ==
    /\ \/ /\ k \in DOMAIN cache[c]
          /\ reads' = [reads EXCEPT ![c][k] = Append(reads[c][k], cache[c][k].version)]
       \/ /\ k \notin DOMAIN cache[c]
          /\ k \in DOMAIN state
          /\ reads' = [reads EXCEPT ![c][k] = Append(reads[c][k], state[k].version)]
       \/ /\ k \notin DOMAIN cache[c]
          /\ k \notin DOMAIN state
          /\ reads' = [reads EXCEPT ![c][k] = Append(reads[c][k], version)]
    /\ UNCHANGED <<state, pending, cache, cache, events, version>>

\* Put a key/value pair in the map
Put(c, k, v) ==
    /\ version' = version + 1
    /\ LET entry == [key |-> k, value |-> v, version |-> version'] 
       IN
          /\ state' = PutEntry(state, entry)
          /\ events' = [i \in Client |-> Append(events[i], entry)]
          /\ pending' = [pending EXCEPT ![c] = pending[c] @@ (entry.version :> entry)]
    /\ UNCHANGED <<cache, reads>>

\* Remove a key from the map
Remove(c, k) ==
    /\ k \in DOMAIN state
    /\ version' = version + 1
    /\ LET entry == [key |-> k, value |-> Nil, version |-> version']
       IN
          /\ state' = DropKey(state, k)
          /\ events' = [i \in Client |-> Append(events[i], entry)]
          /\ pending' = [pending EXCEPT ![c] = pending[c] @@ (entry.version :> entry)]
    /\ UNCHANGED <<cache, reads>>

\* Cache an entry in the map
Cache(c, e) ==
    /\ LET entry == pending[c][e]
       IN
          /\ \/ /\ entry.value # Nil
                /\ cache' = [cache EXCEPT ![c] = PutEntry(cache[c], entry)]
             \/ /\ entry.value = Nil
                /\ cache' = [cache EXCEPT ![c] = DropKey(cache[c], entry.key)]
          /\ pending' = [pending EXCEPT ![c] = [v \in DOMAIN pending[c] \ {entry.version} |-> pending[c][v]]]
    /\ UNCHANGED <<state, events, version, reads>>

\* Learn of a map update
Learn(c) ==
    /\ Cardinality(DOMAIN events[c]) > 0
    /\ LET entry == events[c][1]
       IN
          \/ /\ entry.key \in DOMAIN cache[c]
             /\ entry.version > cache[c][entry.key].version
             /\ \/ /\ entry.value # Nil
                   /\ cache' = [cache EXCEPT ![c] = PutEntry(cache[c], entry)]
                \/ /\ entry.value = Nil
                   /\ cache' = [cache EXCEPT ![c] = DropKey(cache[c], entry.key)]
          \/ /\ \/ entry.key \notin DOMAIN cache[c]
                \/ /\ entry.key \in DOMAIN cache[c]
                   /\ entry.version <= cache[c][entry.key].version
             /\ UNCHANGED <<cache>>
    /\ events' = [events EXCEPT ![c] = SubSeq(events[c], 2, Len(events[c]))]
    /\ UNCHANGED <<state, pending, version, reads>>

\* Evict a map entry from the cache
Evict(c, k) ==
    /\ k \in DOMAIN cache[c]
    /\ cache' = [cache EXCEPT ![c] = DropKey(cache[c], k)]
    /\ UNCHANGED <<state, pending, events, version, reads>>

----

Init ==
    /\ LET nilEntry == [key |-> Nil, value |-> Nil, version |-> Nil]
       IN
          /\ state = [i \in {} |-> nilEntry]
          /\ cache = [c \in Client |-> [i \in {} |-> nilEntry]]
          /\ pending = [c \in Client |-> [i \in {} |-> nilEntry]]
          /\ events = [c \in Client |-> [i \in {} |-> nilEntry]]
    /\ version = 0
    /\ reads = [c \in Client |-> [k \in Key |-> <<>>]]

Next ==
    \/ \E c \in Client : 
          \E k \in Key : 
             Get(c, k)
    \/ \E c \in Client : 
          \E k \in Key : 
             \E v \in Value : 
                Put(c, k, v)
    \/ \E c \in Client : 
          \E k \in Key : 
             Remove(c, k)
    \/ \E c \in Client : 
          \E e \in DOMAIN pending[c] : 
             Cache(c, e)
    \/ \E c \in Client : 
          Learn(c)
    \/ \E c \in Client : 
          \E k \in Key : 
             Evict(c, k)

Spec == Init /\ [][Next]_<<vars>>

=============================================================================
\* Modification History
\* Last modified Tue Feb 11 10:21:59 PST 2020 by jordanhalterman
\* Created Mon Feb 10 23:01:48 PST 2020 by jordanhalterman
