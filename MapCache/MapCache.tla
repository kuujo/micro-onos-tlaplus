------------------------------ MODULE MapCache ------------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* An empty value
CONSTANT Nil

\* The set of possible keys
CONSTANT Key

\* The set of possible values
CONSTANT Value

\* The system state
VARIABLE state

\* The cache state
VARIABLE cache

\* A sequence of update events
VARIABLE events

\* The maximum version assigned to an event
VARIABLE version

\* The history of reads for the client; used by the model checker to verify sequential consistency
VARIABLE reads

vars == <<state, cache, events, version>>

----

\* The type invariant checks that the client's reads never go back in time
TypeInvariant ==
    /\ \A r \in DOMAIN reads :
          r > 1 => reads[r] > reads[r-1]

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

\* Cache a map entry
Cache(entry) == cache' = PutEntry(cache, entry)

\* Evict a map key from the cache
Evict(k) == cache' = DropKey(cache, k)

----

(*
This section models the method calls for the Map primitive.
Map entries can be created, updated, deleted, and read. When the map state is changed,
events are enqueued for the client, and the learner updates the cache.
*)

\* Get a value/version for a key in the map
Get(k) ==
    /\ \/ /\ k \in DOMAIN cache
          /\ reads' = Append(reads, cache[k].version)
       \/ /\ k \notin DOMAIN cache
          /\ k \in DOMAIN state
          /\ reads' = Append(reads, state[k].version)
       \/ /\ k \notin DOMAIN cache
          /\ k \notin DOMAIN state
          /\ reads' = Append(reads, version)
    /\ UNCHANGED <<state, cache, events, version>>

\* Put a key/value pair in the map
Put(k, v) ==
    /\ version' = version + 1
    /\ LET entry == [key |-> k, value |-> v, version |-> version'] 
       IN
          /\ state' = PutEntry(state, entry)
          /\ events' = Append(events, entry)
          /\ Evict(k)
    /\ UNCHANGED <<reads>>

\* Remove a key from the map
Remove(k) ==
    /\ version' = version + 1
    /\ LET entry == [key |-> k, version |-> version']
       IN
          /\ state' = DropKey(state, k)
          /\ events' = Append(events, entry)
          /\ Evict(k)
    /\ UNCHANGED <<reads>>

\* Learn of a map update
Learn ==
    /\ Cardinality(DOMAIN events) > 0
    /\ Cache(events[1])
    /\ events' = SubSeq(events, 2, Len(events))
    /\ UNCHANGED <<state, version, reads>>

----

Init ==
    /\ state = [i \in {} |-> [key |-> Nil, value |-> Nil, version |-> Nil]]
    /\ cache = [i \in {} |-> [key |-> Nil, value |-> Nil, version |-> Nil]]
    /\ events = [i \in {} |-> [key |-> Nil, value |-> Nil, version |-> Nil]]
    /\ version = 0
    /\ reads = [i \in {} |-> 0]

Next ==
    \/ \E k \in Key : 
          \E v \in Value : Put(k, v)
    \/ \E k \in Key : Get(k)
    \/ \E k \in Key : Remove(k)
    \/ Learn

Spec == Init /\ [][Next]_<<vars>>

=============================================================================
\* Modification History
\* Last modified Tue Feb 11 00:50:25 PST 2020 by jordanhalterman
\* Created Mon Feb 10 23:01:48 PST 2020 by jordanhalterman
