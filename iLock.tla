
------------------------ MODULE AsyncMutex------------------------
EXTENDS Integers , Naturals, Sequences, FiniteSets

CONSTANTS  Actors, Mutexes, LockIns, UnlockIns, MwaitIns
VARIABLES pc, waitingQueue, Requests

NoActor == CHOOSE a : a \notin Actors

Partition(S) == \forall x,y \in S : x \cap y /= {} => x = y
Instr ==UNION {LockIns, UnlockIns, MwaitIns}


           
getIndex(e,q) == CHOOSE n \in DOMAIN q : q[n] = e


isHead(m,q) == IF q = <<>> THEN FALSE  
                ELSE IF m = Head(q) THEN  TRUE
                     ELSE FALSE 

isMember(m, q) == IF \E i \in (1..Len(q)): m = q[i] THEN TRUE
                  ELSE FALSE

Remove(e,q) == SubSeq(q, 1, getIndex(e,q)-1) \circ SubSeq(q, getIndex(e,q)+1, Len(q))
    



MutexAsyncLock(Aid, mid) ==
   /\ Aid \in Actors
   /\ pc[Aid] \in LockIns
   /\ mid \in Mutexes
   /\ \/ /\ ~isMember(Aid, waitingQueue[mid]) 
         /\ Requests'  = [Requests EXCEPT ![Aid]= Requests[Aid] \cup {mid}]
         /\ waitingQueue' = [waitingQueue EXCEPT ![mid] = Append(waitingQueue[mid], Aid)] 
      \/ /\ isMember(Aid, waitingQueue[mid]) 
         /\ UNCHANGED <<waitingQueue, Requests>>  
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]

(* When a Actoress <Aid> does a valid unlock() on Mutex <mid>, then:
 * - If <Aid> is the owner (head of waitingQueue), that's a naive unlock and we 
 *     remove all linking between Aid and mid that was created in ilock().
 * - If <Aid> is not the owner, that's a cancel, and we remove the linking anyway.
 *
 * - If <Aid> is not even in the waitingQueue (it did not ask for the <mid> previously),
 *   that's not enabled, and <Aid> is blocked. Too bad for it.
 *)
MutexUnlock(Aid, mid) ==
   /\ Aid \in Actors
   /\ mid \in Mutexes
   /\ pc[Aid] \in UnlockIns
   
   (* If the request was previously posted (either owner or not) remove any linking *)
   /\ isMember(Aid, waitingQueue[mid]) 
   /\ waitingQueue' = [waitingQueue EXCEPT ![mid] = Remove(Aid,waitingQueue[mid])]
   /\ Requests' = [Requests EXCEPT ![Aid] = Requests[Aid] \ {mid}]
   (* If not a member, the transition is not enabled *)
   
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]

(* When a Actoress <Aid> does a mutex_wait on <mid>, 
 *  - If <Aid> is the owner of <mid>, then MutexWait is fined
 *  - If not, the transition is not enabled
 *)


MutexWait(Aid, mid) == 
/\ Aid \in Actors
/\ mid \in Mutexes
/\ pc[Aid] \in MwaitIns
/\ isHead(Aid, waitingQueue[mid]) (* transition enabled iff Aid is owner *)
/\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
/\ UNCHANGED << waitingQueue, Requests>>


Init == 
        /\ waitingQueue = [i \in Mutexes |-> << >>]
        /\ Requests = [i \in Actors |-> {}]
        /\ pc = CHOOSE f \in [Actors -> Instr] : TRUE
         (*/\ pc = [a \in Actors |-> "lock"] *)

Next == \exists actor \in Actors, mutex \in Mutexes :
          \/ MutexAsyncLock(actor,mutex)
          \/ MutexUnlock(actor,mutex)
          \/ MutexWait(actor, mutex)
         (* \/ Mtest(p,reqs, test_r) *)

TCConsistent ==  ~ \E a1, a2    \in Actors : 
                                /\ pc[a1] ="lock"
                                /\ pc[a2] ="unlock"
                                
                                /\ a1 /= a2
                             
 Spec == Init /\ [][Next]_<<waitingQueue, Requests>>   

=============================================================================
