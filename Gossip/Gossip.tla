------------------------------- MODULE Gossip -------------------------------


=============================================================================
\* Modification History
\* Last modified Wed Oct 22 09:34:46 IST 2025 by srikar
\* Created Tue Oct 21 23:37:45 IST 2025 by srikar
--------------------------- MODULE VersionVector ---------------------------
(***************************************************************************
 * A TLA+ specification of a distributed version vector system with gossip
 * 
 * This models a set of servers that maintain version vectors to track
 * distributed state. Each server maintains a vector of version numbers,
 * one for each server in the system.
 * 
 * Key operations:
 * - Bump: A server increments its own version counter
 * - Gossip: Two servers exchange and merge their version vectors
 * - Restart: A server crashes and loses knowledge of other servers' versions
 ***************************************************************************)

CONSTANT servers  
    (* The set of all servers in the system, e.g., {s1, s2, s3} *)

VARIABLE version  
    (* version[i][j] represents server i's knowledge of server j's version.
     * This is a function: servers -> (servers -> Nat)
     * 
     * Example with 2 servers:
     * version[s1][s1] = 3  means s1 knows its own version is 3
     * version[s1][s2] = 2  means s1 thinks s2's version is 2
     * version[s2][s1] = 1  means s2 thinks s1's version is 1
     *)

Max_Version == 3
    (* Maximum version number a server can reach.
     * Used to create a bounded state space for model checking.
     *)

vars == <<version>>
    (* Tuple of all state variables - required for fairness conditions *)

-----------------------------------------------------------------------------
(* INITIAL STATE *)

Init == 
    (* All servers start with version 0 for all servers (including themselves).
     * This represents a fresh system where no events have occurred yet.
     *)
    version = [i \in servers |-> [j \in servers |-> 0]]

-----------------------------------------------------------------------------
(* ACTIONS - State Transitions *)

Gossip(i, j) == 
    (* Server i and server j exchange their version vectors and merge them.
     * 
     * The merge operation takes the MAX of each component:
     * - If i thinks j is at version 5, and j thinks j is at version 7,
     *   after gossip both will agree j is at version 7.
     * 
     * This models eventual consistency - information flows through gossip.
     * 
     * Parameters:
     *   i, j: The two servers that are gossiping
     * 
     * Effect:
     *   Both servers update their version vectors to the component-wise
     *   maximum of their previous vectors.
     *)
    LET 
        (* Helper function: return the maximum of two numbers *)
        Max(a, b) == IF a > b THEN a ELSE b 
        
        (* Compute the merged vector: take max of each component
         * updated[k] = max(version[i][k], version[j][k])
         * This means: take the higher version number for server k
         *)
        updated == [k \in servers |-> Max(version[i][k], version[j][k])]
        
        (* Update server i's vector to the merged result *)
        version_a == [version EXCEPT ![i] = updated] 
        
        (* Update server j's vector to the merged result
         * IMPORTANT: This is based on version_a, not the original version.
         * This ensures both updates happen atomically in the same step.
         *)
        version_ab == [version_a EXCEPT ![j] = updated]
    IN 
        version' = version_ab 

Bump(i) == 
    (* Server i increments its own version counter by 1.
     * 
     * This represents a local event at server i (e.g., processing a write,
     * handling a request, etc.). The server only updates its own counter.
     * 
     * Parameters:
     *   i: The server that is bumping its version
     * 
     * Precondition:
     *   The server hasn't reached Max_Version yet
     * 
     * Effect:
     *   version[i][i] increases by 1, all other entries unchanged
     * 
     * Note: ![i][i] is nested EXCEPT syntax - updates version[i][i] directly
     *)
    /\ version[i][i] /= Max_Version
        (* Guard: Only bump if we haven't reached the maximum *)
    
    /\ version' = [version EXCEPT ![i][i] = version[i][i] + 1]
        (* Directly increment version[i][i], all other entries stay the same *)

Restart(i) == 
    (* Server i crashes and restarts, losing its knowledge of other servers.
     * 
     * After a restart, the server remembers its own version counter
     * (perhaps stored on disk) but loses all knowledge of other servers'
     * versions (in-memory state is lost).
     * 
     * Parameters:
     *   i: The server that is restarting
     * 
     * Effect:
     *   version[i][j] = 0 for all j != i (loses knowledge of others)
     *   version[i][i] unchanged (own counter persists)
     * 
     * This models the CAP theorem tradeoff - availability (server can restart)
     * vs consistency (loses sync state).
     *)
    version' = [version EXCEPT ![i] = [k \in servers |->  
        IF k /= i 
        THEN 0                      (* Reset knowledge of other servers *)
        ELSE version[i][i]]]        (* Keep own version counter *)

Next == 
    (* The next-state relation: at least one of these actions occurs.
     * 
     * The \/ is logical OR, so in each step, the system can:
     * - Have some server bump its version, OR
     * - Have two servers gossip, OR  
     * - Have some server restart
     * 
     * \E means "there exists" - picks nondeterministically from servers.
     *)
    \/ \E i \in servers: Bump(i)
    \/ \E i, j \in servers: Gossip(i, j) 
    \/ \E i \in servers: Restart(i)

-----------------------------------------------------------------------------
(* SAFETY PROPERTIES - Things that should always be true *)

Safety == 
    (* Version numbers are always bounded and non-negative.
     * 
     * This should be an invariant - true in all reachable states.
     * Model checker verifies this holds after every step.
     *)
    \A i, j \in servers: 
        /\ version[i][j] >= 0               (* No negative versions *)
        /\ version[i][j] <= Max_Version     (* Doesn't exceed maximum *)

-----------------------------------------------------------------------------
(* LIVENESS PROPERTIES - Things that should eventually happen *)

EventualConvergence == 
    (* Eventually, all servers have identical version vectors.
     * 
     * This is weak - it only requires convergence to happen once.
     * After convergence, servers could diverge again (due to Restart).
     * 
     * <>P means "eventually P" (P is true in some future state)
     *)
    <>(\A i, j \in servers: version[i] = version[j])

EventualStability ==
    (* Eventually, all servers converge and stay converged forever.
     * 
     * This is stronger - requires sustained convergence.
     * Likely NOT satisfied if Restart has weak fairness.
     * 
     * <>[]P means "eventually always P" (P becomes permanently true)
     *)
    <>[](\A i, j \in servers: version[i] = version[j])

Monotonicity ==
    (* Version vectors never decrease - only increase or stay same.
     * 
     * This should be true because:
     * - Bump only increases values
     * - Gossip takes MAX (never decreases)
     * - Restart can decrease, but only for non-local entries
     * 
     * [][A]_vars means "always A, or vars don't change"
     *)
    [][\A i, j \in servers: 
        \A k \in servers: version'[i][k] >= version[i][k]]_vars

EventualPropagation ==
    (* If a server reaches a version, all others eventually learn about it.
     * 
     * This captures the gossip protocol's key guarantee:
     * information eventually disseminates through the system.
     * 
     * P ~> Q means "P leads to Q" (if P becomes true, Q eventually follows)
     * 
     * NOTE: This may not hold with Restart, since restarting servers
     * lose their knowledge.
     *)
    \A i, j \in servers: 
        (version[i][i] = Max_Version) ~> (version[j][i] = Max_Version)

WeakLiveness == 
    (* Original liveness property - checks if all servers eventually
     * see all versions at maximum.
     * 
     * This is quite weak because:
     * - Uses <> not <>[], so only needs to happen once
     * - Only checks the Max_Version case
     * - Likely not satisfiable with Restart enabled
     *)
    \A i, j \in servers:
        (i /= j) => 
            (<>(version[i][i] = Max_Version /\ version[i][j] = Max_Version /\
                version[j][i] = Max_Version /\ version[j][j] = Max_Version))

-----------------------------------------------------------------------------
(* SPECIFICATION - Complete system behavior *)

Spec == 
    (* The complete specification combines:
     * 1. Initial state
     * 2. Next-state relation (what steps are possible)
     * 3. Fairness conditions (what steps must eventually happen)
     *)
    /\ Init 
    
    /\ [][Next]_vars
        (* In each step: either Next occurs, or vars don't change (stuttering).
         * Stuttering is allowed to compose specifications.
         *)
    
    /\ \A i \in servers: WF_vars(Bump(i))
        (* Weak fairness for Bump: if Bump(i) is continuously enabled,
         * it must eventually execute. This prevents servers from being
         * starved - each server eventually gets to increment its version.
         *)
    
    /\ \A i, j \in servers: WF_vars(Gossip(i, j))
        (* Weak fairness for Gossip: if two servers can gossip, they
         * eventually do. This ensures information propagates through
         * the system rather than being trapped at individual nodes.
         *)
    
    (* NOTE: No fairness for Restart! 
     * Restarts are failures - they happen arbitrarily, not "fairly".
     * We don't want to require servers to crash.
     *)

=============================================================================

(***************************************************************************
 * MODEL CHECKING CONFIGURATION
 * 
 * To check this spec in TLC, create a model with:
 * 
 * CONSTANTS:
 *   servers <- {s1, s2, s3}  (or any finite set)
 * 
 * INVARIANTS to check:
 *   Safety
 *   Monotonicity (if Restart disabled)
 * 
 * PROPERTIES to check:
 *   EventualConvergence (without Restart fairness)
 *   EventualPropagation (without Restart fairness)
 * 
 * STATE CONSTRAINT (to limit state space):
 *   \A i, j \in servers: version[i][j] <= Max_Version
 * 
 ***************************************************************************)