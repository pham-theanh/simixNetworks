----------------------------- MODULE iLock -----------------------------
EXTENDS Integers , Naturals, Sequences, FiniteSets

CONSTANT Proc, Mutex, ValTrue, ValFalse, Addr,
          UnlockIns, MtestIns, MwaitIns, IlockIns
VARIABLES pc, waitedQueue, memory, request

Partition(S) == \forall x,y \in S : x \cap y /= {} => x = y
Instr ==UNION {IlockIns, UnlockIns, MtestIns, MwaitIns}

isHead(m,q) == IF q = <<>> THEN FALSE  
                ELSE IF m = Head(q) THEN  TRUE
                     ELSE FALSE 


isContain(m,q) == IF \E i \in (1..Len(q)): m = q[i] THEN TRUE
                    ELSE FALSE


lockRequest == [id: Nat,
                process: Proc,
                mutex: Mutex
           ]



Ilock(pid,mid, req_r) ==
   /\ pid \in Proc
   /\ pc[pid] \in IlockIns
   /\ mid \in Mutex
   /\ req_r \in Addr
   (* asssume I can not do ilock if I have a request of 
   ilock of the same mutex need to be processed*)
   /\ ~isContain(waitedQueue[mid],pid) 
   /\ LET  req ==  
                  [id |-> Cardinality(request)+1, 
                   process |-> pid,
                   mutex |-> mid]
      IN /\ request'  = request \cup {req}
         /\ memory' = [memory EXCEPT ![pid][req_r] = req.id]  (*store request's id in the memory*)
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
   /\ waitedQueue' = [waitedQueue EXCEPT ![mid] = Append(waitedQueue[mid],pid)]  

(*unlock does not need to follow a Mtest or Mwait in this version*)
   
Unlock(pid, mid) ==
   /\ pid \in Proc
   /\ mid \in Mutex
   /\ pc[pid] \in UnlockIns
   /\ isHead(pid,waitedQueue[mid])
   /\ waitedQueue' = [waitedQueue EXCEPT ![mid] = Tail(waitedQueue[mid])] 
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
   /\ UNCHANGED <<memory, request>>

(* Mtest = Test_any *)

Mtest(pid, reqs,test_r) ==
  /\ pid \in Proc
  /\ pc[pid] \in MwaitIns
  /\ test_r \in Addr
  /\ reqs \subseteq Addr
  /\ \/ \E req \in reqs, r \in request: r.id = memory[pid][req] 
        /\ isHead(pid,waitedQueue[r.mid])
        /\ request' = (request \ {r})
        /\ memory' = [memory EXCEPT ![pid][test_r] = ValTrue]
     \/ ~\E req \in reqs, r \in reqs: r.id = memory[pid][req]       
        /\ isHead(pid,waitedQueue[r.mid])
        /\ memory' = [memory EXCEPT ![pid][test_r] = ValFalse]
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]


(* Mwait = wait_any*)

Mwait(pid, reqs) ==
  /\ pid \in Proc
  /\ pc[pid] \in MwaitIns
  /\ reqs \subseteq Addr
  /\ \E req \in reqs, r \in request: r.id = memory[pid][req]
        /\ isHead(pid,waitedQueue[r.mid])
        /\ request' = (request \ {r})
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]


Init == 
        /\ waitedQueue = [i \in Mutex |-> << >>]
        /\ pc = CHOOSE f \in [Proc -> Instr] : TRUE
        /\ memory  \in [Proc -> [Mutex -> Nat]]


Next == \exists p \in Proc, mutex \in Mutex, req \in Addr, test_r \in Addr:
          \/ Ilock(p,mutex, req)
          \/ Unlock(p,mutex)
          \/ Mwait(p, mutex)
          \/ Mtest(p,mutex, test_r)



   
Spec == Init /\ [][Next]_<<pc,waitedQueue, memory>>        

=============================================================================
\* Modification History
\* Last modified Fri Jan 19 16:43:16 CET 2018 by diep-chi
\* Created Thu Dec 14 10:59:35 CET 2017 by diep-chi
