----------------------------- MODULE iLock -----------------------------
EXTENDS Integers , Naturals, Sequences, FiniteSets

CONSTANT Proc, Mutex, ValTrue, ValFalse, Addr,
          UnlockIns, MtestIns, MwaitIns, IlockIns

(* Process-specific variables (ie, generic variables used by all submodules)
    - pc[pid] is the next instruction that pid should execute
   Mutex-specific variables
    - waitingQueue[mid] is a fifo list of <pid>s that have a pending request
    - requests[pid] is set of <mid> for which <pid> has a pending requests
*)

VARIABLES pc, waitingQueue, requests

(* unused variable in this module: memory.
   - memory[pid][addr] is a value. It means that each pid have a separate memory area
*)

Partition(S) == \forall x,y \in S : x \cap y /= {} => x = y
Instr ==UNION {IlockIns, UnlockIns, MtestIns, MwaitIns}

isHead(m,q) == IF q = <<>> THEN FALSE  
               ELSE IF m = Head(q) THEN  TRUE
                     ELSE FALSE 


isMember(m, q) == IF \E i \in (1..Len(q)): m = q[i] THEN TRUE
                  ELSE FALSE

getIndex(e,q) == CHOOSE n \in DOMAIN q : q[n] = e

Remove(e,q) == SubSeq(q, 1, getIndex(e,q)-1) \circ SubSeq(q, getIndex(e,q)+1, Len(q))

-------------------------------------------------------------------------

(* When a process <pid> does a valid lock_async() on Mutex <mid>, then:
 *    - <mid> is added to request[pid]
 *    - <pid> is added to the tail of waitingQueue[mid]
 * ilock is invalid if <pid> already has a pending request on <mid> (that's a no-op)
 *)


MutexAsyncLock(pid, mid) ==
   /\ pid \in Proc
   /\ pc[pid] \in IlockIns
   /\ mid \in Mutex
   /\ \/ /\ ~isMember(pid, waitingQueue[mid]) 
         /\ requests'  = [requests EXCEPT ![pid]= requests[pid] \cup {mid}]
         /\ waitingQueue' = [waitingQueue EXCEPT ![mid] = Append(waitingQueue[mid],pid)] 
      \/ /\ isMember(pid, waitingQueue[mid]) 
         /\ UNCHANGED <<waitingQueue, requests,network, testMemory>>  
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]

(* When a process <pid> does a valid unlock() on Mutex <mid>, then:
 * - If <pid> is the owner (head of waitingQueue), that's a naive unlock and we 
 *     remove all linking between pid and mid that was created in ilock().
 * - If <pid> is not the owner, that's a cancel, and we remove the linking anyway.
 *
 * - If <pid> is not even in hte waitingQueue (it did not ask for the <mid> previously),
 *   that's not enabled, and <pid> is blocked. Too bad for it.
 *)
MutexUnlock(pid, mid) ==
   /\ pid \in Proc
   /\ mid \in Mutex
   /\ pc[pid] \in UnlockIns
   
   (* If the request was previously posted (either owner or not) remove any linking *)
   /\ isMember(pid, waitingQueue[mid]) 
   /\ waitingQueue' = [waitingQueue EXCEPT ![mid] = Remove(pid,waitingQueue[mid])]
   /\ requests' = [requests EXCEPT ![pid] = requests[pid] \ {mid}]
   (* If not a member, the transition is not enabled *)
   
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
   /\ UNCHANGED <<network, testMemory>>  


(* When a process <pid> does a mutex_wait on <mid>, 
 *  - If <pid> is the owner of <mid>, then proceed
 *  - If not, the transition is not enabled
 *)



mutex_wait(pid, mid) == 
   /\ pid \in Proc
   /\ mid \in Mutex
   /\ pc[pid] \in MwaitIns

   /\ isHead(pid, waitingQueue[mid]) (* transition enabled iff pid is owner *)

   /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
   /\ UNCHANGED <<waitingQueue, requests>>


(* mutex_test() is messy because it's not an instruction, but a boolean function that is
 *  used in transitions of the application.
 *
 * Solution 1: make a transtion that is a no-op, ignoring the side effects of the
 *  return value, arguing that the model is not fine-grained enough. But it's bad because
 *  we do know that mutex_test() and mutex_unlock() are actually dependent.
 *
 * Solution 2: make a pure function, just like isHead(). But if it's not a transition,
 *  we cannot evaluate whether it's (in)dependent with other transitions.
 *  We don't want to consider each and every application's transition here.
 *
 * Solution 3: split it into 2 transitions, mutex_test_true() and mutex_test_false() that
 *  are enabled only when they can go through.
 * 
 *)
mutex_test(pid, mid) =
   \/ mutex_test_true(pid, mid)
   \/ mutex_test_false(pid, mid)

mutex_test_true(pid, mid) == 
   /\ pid \in Proc
   /\ mid \in Mutex
   /\ pc[pid] \in MtestIns
   
   /\ isHead(pid, waitingQueue[mid])
   
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
   /\ UNCHANGED <<waitingQueue, requests>>

mutex_test_false(pid, mid) == 
   /\ pid \in Proc
   /\ mid \in Mutex
   /\ pc[pid] \in MtestIns
   
   /\ ~isHead(pid, waitingQueue[mid])
   
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
   /\ UNCHANGED <<waitingQueue, requests>>


(* Remaining TODO:
  - mutex_wait_any() and mutex_test_any()
  - see how to combine with communication module, maybe.



(*Mwait_any. the wait is fired if at least one request (r)
whose process (pid) is the owner of the mutex (r.mutex), r is removed from set request *)

Mwait_any(pid, reqs) ==
  /\ pid \in Proc
  /\ pc[pid] \in MwaitIns
  /\ reqs \subseteq Addr
  /\ \E req \in reqs, r \in requests: /\ r.id = memory[pid][req]
        /\ isHead(pid,waitingQueue[r.mutex])
        /\ requests' = (requests \ {r})
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
  /\ UNCHANGED <<waitingQueue, memory>>
*)
------------------------------------------------------------------------------------------------------
(*Initiate the variables*)

Init == 
        /\ waitingQueue = [i \in Mutex |-> << >>]
        /\ pc = CHOOSE f \in [Proc -> Instr] : TRUE
        (*/\ pc = [i \in Proc |-> "ilock"]*)
        /\ memory  \in [Proc -> [Addr -> {0}]]
        /\ requests = {}

Next == \exists p \in Proc, mutex \in Mutex, req_a \in Addr  , test_r \in Addr, reqs \in SUBSET Addr:
          \/ MutexAsyncLock(p,mutex, req_a)
          \/ MutexUnlock(p,mutex)
          \/ Mwait(p, reqs)
          \/ Mtest(p,reqs, test_r)

(*TCConsistent ==  ~ \E p1, p2    \in Proc : 
                                /\ pc[p1] ="ilock"
                                /\ pc[p2] ="unlock"
                                
                                /\ p1 /= p2*)
                             
 Spec == Init /\ [][Next]_<<pc,waitingQueue, memory,requests>>     
-----------------------------------------------------------------------------------------------------
(* Independence operator *)
I(A,B) == ENABLED A /\ ENABLED B => /\ A => (ENABLED B)'
                                    /\ B => (ENABLED A)'
                                    /\ A \cdot B \equiv B \cdot A
                              
THEOREM \forall p1, p2 \in Proc: \forall mutex1, mutex2 \in Mutex: \forall req1, req2 \in Addr:  
        /\ p1 /= p2
        /\ ENABLED Ilock(p1,mutex1, req1)
        /\ ENABLED Ilock(p2,mutex2, req2)
        => I(Ilock(p1,mutex1, req1), Ilock(p2,mutex2, req2))   
================================================================================================
\* Modification History
\* Last modified Wed Jan 31 14:06:50 CET 2018 by diep-chi
\* Created Thu Dec 14 10:59:35 CET 2017 by diep-chi
