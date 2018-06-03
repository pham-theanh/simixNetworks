------------------------- MODULE CompleteAsynMutex -------------------------
EXTENDS TLC, Integers , Naturals, Sequences, FiniteSets

CONSTANTS  Actors, Mutexes, LockIns, UnlockIns, MwaitIns, MtestIns,ValTrue, ValFalse, Addr
VARIABLES  pc, waitingQueue, Requests,  memory

NoActor == CHOOSE a : a \notin Actors

Partition(S) == \forall x,y \in S : x \cap y /= {} => x = y
Instr ==UNION {LockIns, MwaitIns(*, MtestIns, UnlockIns*)}

ASSUME Partition({LockIns,  MwaitIns}) 
           
getIndex(e,q) == CHOOSE n \in DOMAIN q : q[n] = e


isHead(m,q) == IF q = <<>> THEN FALSE  
                ELSE IF m = Head(q) THEN  TRUE
                     ELSE FALSE 

chose(S) == CHOOSE i : i \in S

isMember(m, q) == IF \E i \in (1..Len(q)): m = q[i] THEN TRUE
                  ELSE FALSE

Remove(e,q) == SubSeq(q, 1, getIndex(e,q)-1) \circ SubSeq(q, getIndex(e,q)+1, Len(q))
    
---------------------------------------------------------------------------------------


(* When an Actor execute a Lock on a mutex:
- If the actor has a pending request on the mutex, it can not create a new request on the mutex
- else :   
    +Create a request, adding it in actor's request set
    +Store id (id of mutex) of the request in the memory
*)

MutexAsyncLock(Aid, mid, req_a) ==
   /\ Aid \in Actors
   /\ pc[Aid] \in LockIns
   /\ mid \in Mutexes
   /\ req_a \in Addr
   /\ \/ /\ ~isMember(Aid, waitingQueue[mid])
         /\ Requests'  = [Requests EXCEPT ![Aid]= Requests[Aid] \cup {mid}]
         /\ memory' = [memory EXCEPT ![Aid][req_a] = mid]  
         /\ waitingQueue' = [waitingQueue EXCEPT ![mid] = Append(waitingQueue[mid], Aid)]
      \/ /\ isMember(Aid, waitingQueue[mid]) 
         /\ UNCHANGED <<waitingQueue,  memory, Requests>>  
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
(*   /\ pcState[Aid] /= "blocked"*)   
   /\ Aid \in Actors
   /\ mid \in Mutexes
   /\ pc[Aid] \in UnlockIns
   
   (* If the request was previously posted (either owner or not) remove any linking *)
   /\ isMember(Aid, waitingQueue[mid]) 
   /\ waitingQueue' = [waitingQueue EXCEPT ![mid] = Remove(Aid,waitingQueue[mid])]
   /\ Requests' = [Requests EXCEPT ![Aid] = Requests[Aid] \ {mid}]
   (* If not a member, the transition is not enabled *)
   /\ UNCHANGED <<memory>>
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
   
 
   
(* When a Actoress <Aid> does a mutex_wait on <mid>, 
 *  - If <Aid> is the owner of <mid>, then MutexWait is fined
 *  - If not, the transition is not enabled
 *)


MutexWait(Aid, req_a) == 
/\ Aid \in Actors
/\ pc[Aid] \in MwaitIns
/\ \E req \in Requests[Aid]: req = memory[Aid][req_a] /\ isHead(Aid, waitingQueue[req])
/\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
/\ UNCHANGED << memory, waitingQueue, Requests>>



Mtest(Aid, req_a,test_r) ==
  /\ Aid \in Actors
  /\ pc[Aid] \in MtestIns
  /\ test_r \in Addr
  /\  \E req \in  Requests[Aid]: req = memory[Aid][req_a]/\ 
        \/ /\ isHead(Aid,waitingQueue[req])
           /\ memory' = [memory EXCEPT ![Aid][test_r] = ValTrue]
        \/ /\ ~isHead(Aid, waitingQueue[req])
        /\ memory' = [memory EXCEPT ![Aid][test_r] = ValFalse] 
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
  /\ UNCHANGED <<waitingQueue, Requests>>

-----------------------------------------------------------------------------------------------



Init == 
          /\ waitingQueue = [i \in Mutexes |-> <<>>] 
          /\ Requests = [i \in Actors |-> {}]
          (*/\ pc = CHOOSE f \in [Actors -> Instr] : TRUE*)
          /\ memory \in [Actors -> [Addr -> {0,1,2,3,4,5,6,7,8,9,0}]]
          (* /\ pc \in [Actor -> Instr]*)
          /\ pc = <<"l", "l">>
         (*/\ pc = [a \in Actors |-> "wait"]*) 
         
         
Next == \exists actor \in Actors, mutex \in Mutexes, req, test_r \in Addr :
          \/ MutexAsyncLock(actor,mutex,req)
          \/ MutexWait(actor, req)
          \/ Mtest(actor,req, test_r) 
          \/ MutexUnlock(actor,mutex) 

                             
Spec == Init /\ [][Next]_<<pc, memory, waitingQueue, Requests>>   


-------------------------------------------------------------------------------------------------




TCConsistent ==  ~\E a1, a2  \in Actors : 
                                /\ a1 /= a2
                                /\ pc[a1] = "wait"
                                /\ pc[a2] = "wait"
                                /\ waitingQueue = << <<2,1>>, <<1,2>> >> 
                                /\ Requests = <<{1,2}, {1,2}>> 
                                

=============================================================================
\* Modification History
\* Last modified Sun Jun 03 10:30:24 CEST 2018 by diep-chi
\* Created Sat Jun 02 14:48:20 CEST 2018 by diep-chi
