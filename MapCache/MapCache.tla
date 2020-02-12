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

\* An update entry type
CONSTANT Update

\* A tombstone entry type
CONSTANT Tombstone

\* The system state
VARIABLE state

\* The maximum version assigned to an event
VARIABLE stateVersion

\* The cache state
VARIABLE cache

\* The maximum version propagated to the cache
VARIABLE cacheVersion

\* A bag of pending cache entries
VARIABLE cachePending

\* A sequence of update events
VARIABLE events

\* The history of reads for the client; used by the model checker to verify sequential consistency
VARIABLE reads

vars == <<state, stateVersion, cache, cachePending, cacheVersion, events, reads>>

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
This section models the cache. When a client updates the map, it defers updates to the
cache to be performed asynchronously. The cache also listens for events coming from
other clients.
*)

\* Defer an entry 'e' to be cached asynchronously on client 'c'
\* Updates are deferred in no particular order to model the potential reordering of
\* concurrent threads by the operating system.
DeferCache(c, e) ==
    cachePending' = [cachePending EXCEPT ![c] = cachePending[c] @@ (e.version :> e)]

\* Cache an entry 'e' on client 'c'
\* The entry is read from the pending cache entries. An entry will only be updated
\* in the cache if the entry version is greater than the cache propagation version,
\* ensuring the cache cannot go back in time.
\* Note that removals are inserted into the cache as tombstones to be removed once
\* updates have been propagated via event queues.
Cache(c, e) ==
    /\ LET entry == cachePending[c][e]
       IN
          /\ \/ /\ entry.version > cacheVersion[c]
                /\ \/ entry.key \notin DOMAIN cache[c]
                   \/ /\ entry.key \in DOMAIN cache[c]
                      /\ entry.version > cache[c][entry.key].version
                /\ cache' = [cache EXCEPT ![c] = PutEntry(cache[c], entry)]
             \/ /\ \/ entry.version <= cacheVersion[c]
                   \/ /\ entry.key \in DOMAIN cache[c]
                      /\ entry.version <= cache[c][entry.key].version
                /\ UNCHANGED <<cache>>
          /\ cachePending' = [cachePending EXCEPT ![c] = [v \in DOMAIN cachePending[c] \ {entry.version} |-> cachePending[c][v]]]
    /\ UNCHANGED <<state, stateVersion, cacheVersion, events, reads>>

\* Enqueue a cache update event 'e' for all clients
EnqueueEvent(e) ==
    events' = [i \in Client |-> Append(events[i], e)]

\* Learn a map update from the event queue of 'c'
\* The learner learns the first entry in the event queue for client 'c'.
\* If the key is already in the cache, the learner updates the key only if
\* the update version is at least as great as the cached version.
\* If the key is not present in the map, the entry is cached.
\* Tombstone types are removed from the cache. Entry types are inserted.
\* Once caching is complete, the 'cacheVersion' is updated to ensure the
\* deferred cache remains consistent.
Learn(c) ==
    /\ Cardinality(DOMAIN events[c]) > 0
    /\ LET entry == events[c][1]
       IN
          /\ \/ /\ entry.key \in DOMAIN cache[c]
                /\ entry.version >= cache[c][entry.key].version
                /\ \/ /\ entry.type = Update
                      /\ cache' = [cache EXCEPT ![c] = PutEntry(cache[c], entry)]
                   \/ /\ entry.type = Tombstone
                      /\ cache' = [cache EXCEPT ![c] = DropKey(cache[c], entry.key)]
             \/ /\ \/ entry.key \notin DOMAIN cache[c]
                   \/ /\ entry.key \in DOMAIN cache[c]
                      /\ entry.version < cache[c][entry.key].version
                /\ UNCHANGED <<cache>>
          /\ cacheVersion' = [cacheVersion EXCEPT ![c] = entry.version]
    /\ events' = [events EXCEPT ![c] = SubSeq(events[c], 2, Len(events[c]))]
    /\ UNCHANGED <<state, stateVersion, cachePending, reads>>

\* Evict a map key 'k' from the cache of client 'c'
Evict(c, k) ==
    /\ k \in DOMAIN cache[c]
    /\ cache' = [cache EXCEPT ![c] = DropKey(cache[c], k)]
    /\ UNCHANGED <<state, stateVersion, cachePending, cacheVersion, events, reads>>

----

(*
This section models the method calls for the Map primitive.
Map entries can be created, updated, deleted, and read. When the map state is changed,
events are enqueued for the client, and the learner updates the cache.
*)

\* Get an entry for key 'k' in the map on client 'c'
\* If the key is present in the cache, read from the cache.
\* If the key is not present in the cache, read from the system state and update the
\* cache if the system entry version is greater than the cache version.
\* If the key is neither present in the cache or the system state, read the cache version.
Get(c, k) ==
    /\ \/ /\ k \in DOMAIN cache[c]
          /\ reads' = [reads EXCEPT ![c][k] = Append(reads[c][k], cache[c][k].version)]
          /\ UNCHANGED <<cache>>
       \/ /\ k \notin DOMAIN cache[c]
          /\ k \in DOMAIN state
          /\ LET entry == state[k]
             IN
                /\ \/ /\ entry.version > cacheVersion[c]
                      /\ cache' = [cache EXCEPT ![c] = PutEntry(cache[c], entry)]
                   \/ /\ entry.version <= cacheVersion[c]
                      /\ UNCHANGED <<cache>>
                /\ reads' = [reads EXCEPT ![c][k] = Append(reads[c][k], state[k].version)]
       \/ /\ k \notin DOMAIN cache[c]
          /\ k \notin DOMAIN state
          /\ reads' = [reads EXCEPT ![c][k] = Append(reads[c][k], cacheVersion[c])]
          /\ UNCHANGED <<cache>>
    /\ UNCHANGED <<state, stateVersion, cachePending, cacheVersion, events>>

\* Put key 'k' and value 'v' pair in the map on client 'c'
\* Increment the system state version and insert the entry into the system state.
\* Enqueue update events to notify all clients and defer a local cache update to
\* client 'c'.
Put(c, k, v) ==
    /\ stateVersion' = stateVersion + 1
    /\ LET entry == [type |-> Update, key |-> k, value |-> v, version |-> stateVersion'] 
       IN
          /\ state' = PutEntry(state, entry)
          /\ EnqueueEvent(entry)
          /\ DeferCache(c, entry)
    /\ UNCHANGED <<cache, cacheVersion, reads>>

\* Remove key 'k' from the map on client 'c'
\* Increment the system state version and remove the entry from the system state.
\* Enqueue tombstone events to notify all clients and defer a local cache update
\* to client 'c'.
Remove(c, k) ==
    /\ k \in DOMAIN state
    /\ stateVersion' = stateVersion + 1
    /\ LET entry == [type |-> Tombstone, key |-> k, value |-> Nil, version |-> stateVersion']
       IN
          /\ state' = DropKey(state, k)
          /\ EnqueueEvent(entry)
          /\ DeferCache(c, entry)
    /\ UNCHANGED <<cache, cacheVersion, reads>>

----

Init ==
    /\ LET nilEntry == [type |-> Nil, key |-> Nil, value |-> Nil, version |-> Nil]
       IN
          /\ state = [i \in {} |-> nilEntry]
          /\ stateVersion = 0
          /\ cache = [c \in Client |-> [i \in {} |-> nilEntry]]
          /\ cachePending = [c \in Client |-> [i \in {} |-> nilEntry]]
          /\ cacheVersion = [c \in Client |-> 0]
          /\ events = [c \in Client |-> [i \in {} |-> nilEntry]]
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
          \E e \in DOMAIN cachePending[c] : 
             Cache(c, e)
    \/ \E c \in Client : 
          Learn(c)
    \/ \E c \in Client : 
          \E k \in Key : 
             Evict(c, k)

Spec == Init /\ [][Next]_<<vars>>

=============================================================================
\* Modification History
\* Last modified Tue Feb 11 13:30:38 PST 2020 by jordanhalterman
\* Created Mon Feb 10 23:01:48 PST 2020 by jordanhalterman
