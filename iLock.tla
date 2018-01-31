----------------------------- MODULE iLock -----------------------------
EXTENDS Integers , Naturals, Sequences, FiniteSets

CONSTANT Proc, Mutex, ValTrue, ValFalse, Addr,
          UnlockIns, MtestIns, MwaitIns, IlockIns
VARIABLES pc, waitedQueue, memory, requests

Partition(S) == \forall x,y \in S : x \cap y /= {} => x = y
Instr ==UNION {IlockIns, UnlockIns, MtestIns, MwaitIns}

isHead(m,q) == IF q = <<>> THEN FALSE  
                ELSE IF m = Head(q) THEN  TRUE
                     ELSE FALSE 


isContain(q,m) == IF \E i \in (1..Len(q)): m = q[i] THEN TRUE
                    ELSE FALSE
(*
lockRequest == [id: Nat,
                process: Proc,
                mutex: Mutex
           ]

*)
-------------------------------------------------------------------------

(*when a process do an ilock, a request req = [id, process, mutex ] will be created. 
req is added to the set request, and id of red is stored in to memory *)

Ilock(pid,mid, req_a) ==
   /\ pid \in Proc
   /\ pc[pid] \in IlockIns
   /\ mid \in Mutex
   /\ req_a \in Addr
   (* asssume I can not do ilock of mutex mid if I am in the wating queue of 
   the that mutex (i have a request of mid need to be processed )*)
   /\ \/ /\~isContain(waitedQueue[mid],pid) 
         /\ LET  req ==  
                  [id |-> Cardinality(requests)+1, 
                   process |-> pid,
                   mutex |-> mid]
            IN /\ requests'  = requests \cup {req}
               /\ memory' = [memory EXCEPT ![pid][req_a] = req.id]  (*store request's id in the memory*)
          /\ waitedQueue' = [waitedQueue EXCEPT ![mid] = Append(waitedQueue[mid],pid)] 
       \/ /\ isContain(waitedQueue[mid],pid) 
          /\ UNCHANGED <<waitedQueue, memory,requests>>  
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]




(*if process pid is the owner (head of waitedQueue[mid] ) of the mutex mid
then we remove pid from the wating queue of the mutex mid. unlock does not 
need to follow a Mtest or Mwait in this version*)
   
Unlock(pid, mid) ==
   /\ pid \in Proc
   /\ mid \in Mutex
   /\ pc[pid] \in UnlockIns
   /\ isHead(pid,waitedQueue[mid])
   /\ waitedQueue' = [waitedQueue EXCEPT ![mid] = Tail(waitedQueue[mid])] 
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
   /\ UNCHANGED <<memory, requests>>





(* Mtest = Test_any. Testing the set of request, if at least one request (r)
whose process (pid) is the owner of the mutex (r.mutex) then return ValTrue 
else return ValFalse. r is removed from the set request if the test returns ValTrue *)
 
Mtest(pid, reqs,test_r) ==
  /\ pid \in Proc
  /\ pc[pid] \in MtestIns
  /\ test_r \in Addr
  /\ reqs \subseteq Addr
  /\ \/ \E req \in reqs, r \in requests: r.id = memory[pid][req] 
        /\ isHead(pid,waitedQueue[r.mutex])
        /\ requests' = (requests \ {r})
        /\ memory' = [memory EXCEPT ![pid][test_r] = ValTrue]
     \/ /\ ~\E req \in reqs, r \in requests: /\ r.id = memory[pid][req]       
            /\ isHead(pid,waitedQueue[r.mutex])
        /\ memory' = [memory EXCEPT ![pid][test_r] = ValFalse] 
        /\ UNCHANGED <<requests>>
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
  /\ UNCHANGED <<waitedQueue>>




(*Mwait = wait_any. the wait is fired if at least one request (r)
whose process (pid) is the owner of the mutex (r.mutex), r is removed from set request *)

Mwait(pid, reqs) ==
  /\ pid \in Proc
  /\ pc[pid] \in MwaitIns
  /\ reqs \subseteq Addr
  /\ \E req \in reqs, r \in requests: /\ r.id = memory[pid][req]
        /\ isHead(pid,waitedQueue[r.mutex])
        /\ requests' = (requests \ {r})
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
  /\ UNCHANGED <<waitedQueue, memory>>
------------------------------------------------------------------------------------------------------
(*Initiate the variables*)

Init == 
        /\ waitedQueue = [i \in Mutex |-> << >>]
        /\ pc = CHOOSE f \in [Proc -> Instr] : TRUE
        (*/\ pc = [i \in Proc |-> "ilock"]*)
        /\ memory  \in [Proc -> [Addr -> {0}]]
        /\ requests = {}

Next == \exists p \in Proc, mutex \in Mutex, req_a \in Addr  , test_r \in Addr, reqs \in SUBSET Addr:
          \/ Ilock(p,mutex, req_a)
          \/ Unlock(p,mutex)
          \/ Mwait(p, reqs)
          \/ Mtest(p,reqs, test_r)

(*TCConsistent ==  ~ \E p1, p2    \in Proc : 
                                /\ pc[p1] ="ilock"
                                /\ pc[p2] ="unlock"
                                
                                /\ p1 /= p2*)
                             
 Spec == Init /\ [][Next]_<<pc,waitedQueue, memory,requests>>     
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
