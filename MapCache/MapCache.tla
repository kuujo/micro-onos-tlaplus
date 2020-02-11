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

\* The current cache version
VARIABLE cacheVersion

\* The highest version read by the client
VARIABLE readVersion

\* A sequence of update events
VARIABLE events

\* The maximum version assigned to an event
VARIABLE version

\* The history of reads for the client; used by the model checker to verify sequential consistency
VARIABLE reads

vars == <<state, cache, cacheVersion, readVersion, events, version, reads>>

----

\* The type invariant checks that the client's reads never go back in time
TypeInvariant ==
    /\ \A k \in Key :
       /\ \A r \in DOMAIN reads[k] :
             r > 1 => reads[k][r] >= reads[k][r-1]

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
Get(k) ==
    /\ \/ /\ cacheVersion >= readVersion
          /\ k \in DOMAIN cache
          /\ reads' = [reads EXCEPT ![k] = Append(reads[k], cache[k].version)]
          /\ UNCHANGED <<readVersion>>
       \/ /\ k \notin DOMAIN cache
          /\ k \in DOMAIN state
          /\ reads' = [reads EXCEPT ![k] = Append(reads[k], state[k].version)]
          /\ readVersion' = state[k].version
       \/ /\ k \notin DOMAIN cache
          /\ k \notin DOMAIN state
          /\ reads' = [reads EXCEPT ![k] = Append(reads[k], version)]
          /\ readVersion' = version
    /\ UNCHANGED <<state, cache, cacheVersion, events, version>>

\* Put a key/value pair in the map
Put(k, v) ==
    /\ version' = version + 1
    /\ LET entry == [key |-> k, value |-> v, version |-> version'] 
       IN
          /\ state' = PutEntry(state, entry)
          /\ events' = Append(events, entry)
          /\ cache' = DropKey(cache, k)
    /\ UNCHANGED <<cacheVersion, readVersion, reads>>

\* Remove a key from the map
Remove(k) ==
    /\ k \in DOMAIN state
    /\ version' = version + 1
    /\ LET entry == [key |-> k, value |-> Nil, version |-> version']
       IN
          /\ state' = DropKey(state, k)
          /\ events' = Append(events, entry)
          /\ cache' = DropKey(cache, k)
    /\ UNCHANGED <<cacheVersion, readVersion, reads>>

\* Learn of a map update
Learn ==
    /\ Cardinality(DOMAIN events) > 0
    /\ LET entry == events[1]
       IN
          /\ \/ /\ entry.value # Nil
                /\ cache' = PutEntry(cache, entry)
             \/ /\ entry.value = Nil
                /\ cache' = DropKey(cache, entry.key)
          /\ cacheVersion' = entry.version
    /\ events' = SubSeq(events, 2, Len(events))
    /\ UNCHANGED <<state, version, readVersion, reads>>

----

Init ==
    /\ state = [i \in {} |-> [key |-> Nil, value |-> Nil, version |-> Nil]]
    /\ cache = [i \in {} |-> [key |-> Nil, value |-> Nil, version |-> Nil]]
    /\ events = [i \in {} |-> [key |-> Nil, value |-> Nil, version |-> Nil]]
    /\ version = 0
    /\ cacheVersion = 0
    /\ readVersion = 0
    /\ reads = [k \in Key |-> <<>>]

Next ==
    \/ \E k \in Key : \E v \in Value : Put(k, v)
    \/ \E k \in Key : Get(k)
    \/ \E k \in Key : Remove(k)
    \/ Learn

Spec == Init /\ [][Next]_<<vars>>

=============================================================================
\* Modification History
\* Last modified Tue Feb 11 02:22:52 PST 2020 by jordanhalterman
\* Created Mon Feb 10 23:01:48 PST 2020 by jordanhalterman
