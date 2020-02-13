------------------------------ MODULE MapCache ------------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* An empty value
CONSTANT Nil

\* The set of clients to model
CONSTANT Client

\* The set of possible keys in the map
CONSTANT Key

\* The set of possible values in the map
CONSTANT Value

\* An update entry identifier
CONSTANT Update

\* A tombstone entry identifier
CONSTANT Tombstone

\* The system state, modelled as a strongly consistent consensus service
\* using a single mapping of key->value pairs
VARIABLE state

\* A sequential version number, used by the consensus service to assign logical 
\* timestamps to entries
VARIABLE stateVersion

\* The cache state
VARIABLE cache

\* The maximum version propagated to the cache
VARIABLE cacheVersion

\* An unordered bag of pending cache entries
VARIABLE cachePending

\* A strongly ordered sequence of update events
VARIABLE events

\* The history of reads for the client, used by the model checker to verify sequential consistency
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
This section models the map cache. When a client updates the map, it defers updates to 
the cache to be performed in a separate step. The cache also listens for events coming 
from a consensus service, which must provide sequentially consistent event streams.
Entries are arbitrarily evicted from the cache.
*)

\* Defer an entry 'e' to be cached asynchronously on client 'c'
\* Updates are deferred in no particular order to model the potential reordering of
\* concurrent threads by the operating system.
DeferCache(c, e) ==
    cachePending' = [cachePending EXCEPT ![c] = cachePending[c] @@ (e.version :> e)]

\* Remove a deferred entry 'e' from cache deferrals for client 'c'
RemoveCacheDeferral(c, e) ==
    cachePending' = [cachePending EXCEPT ![c] = 
        [v \in DOMAIN cachePending[c] \ {e.version} |-> cachePending[c][v]]]

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
          /\ RemoveCacheDeferral(c, entry)
    /\ UNCHANGED <<state, stateVersion, cacheVersion, events, reads>>

\* Enqueue a cache update event 'e' for all clients
\* Events are guaranteed to be delivered to clients in the order in which they
\* occurred in the consensus layer, so we model events as a simple strongly ordered
\* sequence.
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
\* To preserve consistency, each key for each client must be retained until updates 
\* prior to the key version have been propagated to the client. If keys are evicted
\* before updates have been propagated to the cache, evicting a key can allow a 
\* concurrent Put or Remove to cache an older entry.
Evict(c, k) ==
    /\ k \in DOMAIN cache[c]
    /\ cache[c][k].version <= cacheVersion[c]
    /\ cache' = [cache EXCEPT ![c] = DropKey(cache[c], k)]
    /\ UNCHANGED <<state, stateVersion, cachePending, cacheVersion, events, reads>>

----

(*
This section models the method calls for the Map primitive.
Map entries can be created, updated, deleted, and read. The Put and Remove steps
model writes to a consensus service. When the map is updated, write steps do not
atomically cache updates but instead defer them to be cached in a separate step.
This models the reordering of threads by the OS. The Get step models a read of
either the cache or a consensus service. When reading from the consensus service,
the Get step does cache entries atomically since reads can be reordered without
side effects.
*)

\* Get an entry for key 'k' in the map on client 'c'
\* If the key is present in the cache, read from the cache.
\* If the key is not present in the cache, read from the system state and update the
\* cache if the system entry version is greater than the cache version.
\* If the key is neither present in the cache or the system state, read the cache version.
\* Note that the state is read and the cache is updated in a single step. To guarantee
\* consistency, implementations must update the cache before returning.
Get(c, k) ==
    /\ \/ /\ k \in DOMAIN cache[c]
          /\ reads' = [reads EXCEPT ![c][k] = Append(reads[c][k], cache[c][k].version)]
          /\ UNCHANGED <<cache>>
       \/ /\ k \notin DOMAIN cache[c]
          /\ k \in DOMAIN state
          /\ LET entry == state[k]
             IN
                /\ cache' = [cache EXCEPT ![c] = PutEntry(cache[c], entry)]
                /\ reads' = [reads EXCEPT ![c][k] = Append(reads[c][k], state[k].version)]
       \/ /\ k \notin DOMAIN cache[c]
          /\ k \notin DOMAIN state
          /\ LET entry == [type |-> Tombstone, 
                           key |-> k, 
                           value |-> Nil, 
                           version |-> stateVersion]
             IN 
                cache' = [cache EXCEPT ![c] = PutEntry(cache[c], entry)]
          /\ reads' = [reads EXCEPT ![c][k] = Append(reads[c][k], stateVersion)]
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
    /\ LET nilEntry == [type |-> Nil,
                        key |-> Nil, 
                        value |-> Nil, 
                        version |-> Nil]
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
\* Last modified Wed Feb 12 16:52:38 PST 2020 by jordanhalterman
\* Created Mon Feb 10 23:01:48 PST 2020 by jordanhalterman
