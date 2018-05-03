------------------------ MODULE networkSpecification ------------------------

(* This is a TLA module specifying the Communicationsing layer of SIMIX. 
   It is used to verify the soundness of the DPOR reduction algorithm
   used in the model-checker. 

   If you think you found a new independence lemma, add it to this
   file and relaunch TLC to check whether your lemma actually holds.
   *)
EXTENDS Integers , Naturals, Sequences, FiniteSets

CONSTANTS RdV, Addr, Proc, Mutex, ValTrue, ValFalse, SendIns, ReceiveIns, WaitIns, 
          TestIns, LocalIns, LockIns, UnlockIns, MtestIns, MwaitIns
VARIABLES Communications, memory, pc, waitingQueue,Requests

NoProc == CHOOSE p : p \notin Proc
NoAddr == CHOOSE a : a \notin Addr

Partition(S) == \forall x,y \in S : x \cap y /= {} => x = y
Instr ==UNION {SendIns, ReceiveIns, WaitIns, TestIns, LocalIns,LockIns, UnlockIns, MtestIns, MwaitIns}

Comm == [id:Nat,
         rdv:RdV,
         status:{"send","receive","ready","done"},
         src:Proc,
         dst:Proc,
         data_src:Addr,
         data_dst:Addr]
Reqest == [id: Nat,
           pocess: Proc,
           mutex: Mutex
           ]
getIndex(e,q) == CHOOSE n \in DOMAIN q : q[n] = e


isHead(m,q) == IF q = <<>> THEN FALSE  
                ELSE IF m = Head(q) THEN  TRUE
                     ELSE FALSE 

isContain(q,m) == IF \E i \in (1..Len(q)): m = q[i] THEN TRUE
                    ELSE FALSE



isMember(m, q) == IF \E i \in (1..Len(q)): m = q[i] THEN TRUE
                  ELSE FALSE

Remove(e,q) == SubSeq(q, 1, getIndex(e,q)-1) \circ SubSeq(q, getIndex(e,q)+1, Len(q))
    
ASSUME ValTrue \in Nat
ASSUME ValFalse \in Nat

(* The set of all the instructions *)
ASSUME Partition({SendIns, ReceiveIns, WaitIns, TestIns, LocalIns}) 


(* Let's keep everything in the right domains *)
TypeInv == /\ Communications \subseteq Comm
           /\ memory \in [Proc -> [Addr -> Nat]]
           /\ pc \in [Proc -> Instr]

(* The set of all communications waiting at rdv *)
(* ----- mailbox is updated automatically when updating the Communications  *)
mailbox(rdv) == {comm \in Communications : comm.rdv=rdv /\ comm.status \in {"send","receive"}}


(* The set of memory addresses of a process being used in a communication *)
CommBuffers(pid) == 
  {c.data_src: c \in { y \in Communications: y.status /= "done" /\ (y.src = pid \/ y.dst = pid)}} 
\cup {c.data_dst: c \in { y \in Communications: y.status /= "done" /\ (y.src = pid \/ y.dst = pid)}}

(* This is a AsyncSend step of the system *)
(* pid: the process ID of the AsyncSender *)
(* rdv: the rendez-vous point where the "send" communication request is going to be pushed *)
(* data_r: the address in the AsyncSender's memory where the data is stored *)
(* comm_r: the address in the AsyncSender's memory where to store the communication id *)
AsyncSend(pid, rdv, data_r, comm_r) == 
  /\ rdv \in RdV
  /\ pid \in Proc
  /\ data_r \in Addr
  /\ comm_r \in Addr
  /\ pc[pid] \in SendIns
   
     (* A matching AsyncReceive request exists in the rendez-vous *)
     (* Complete the Sender fields and set the communication to the ready state *)
  /\ \/ \exists c \in mailbox(rdv):
          /\ c.status="receive"
          /\ \forall d \in mailbox(rdv): d.status="receive" => c.id <= d.id
          /\ Communications' = 
               (Communications \ {c}) \cup {[c EXCEPT
                                       !.status = "ready",
                                       !.src = pid,
                                       !.data_src = data_r]}
          (* Use c's existing communication id *)
          /\ memory' = [memory EXCEPT ![pid][comm_r] = c.id]
               
     
     (* No matching AsyncReceive communication request exists. *)
     (* Create a AsyncSend request and push it in the Communications. *)
     \/ /\ ~ \exists c \in mailbox(rdv): c.status = "receive" 
        /\ LET comm ==  
                 [id |-> Cardinality(Communications)+1, 
                  rdv |-> rdv,
                  status |-> "send", 
                  src |-> pid,
                  dst |-> NoProc, 
                  data_src |-> data_r,
                  data_dst |-> NoAddr]
           IN
             /\ Communications' = Communications \cup {comm}
             /\ memory' = [memory EXCEPT ![pid][comm_r] = comm.id]           
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
  /\ UNCHANGED <<  waitingQueue,Requests>>
(* This is a receive step of the system *)
(* pid: the process ID of the receiver *)
(* rdv: the Rendez-vous where the "receive" communication request is going to be pushed *)
(* data_r: the address in the receivers's memory where the data is going to be stored *)
(* comm_r: the address in the receivers's memory where to store the communication id *)
AsyncReceive(pid, rdv, data_r, comm_r) == 
  /\ rdv \in RdV
  /\ pid \in Proc
  /\ data_r \in Addr
  /\ comm_r \in Addr
  /\ pc[pid] \in ReceiveIns
  
     (* A matching AsyncSend request exists in the rendez-vous *)
     (* Complete the receiver fields and set the communication to the ready state *)
  /\ \/ \exists c \in mailbox(rdv):
          /\ c.status="send"
          /\ \forall d \in mailbox(rdv): d.status="send" => c.id <= d.id
          /\ Communications' = 
               (Communications \ {c}) \cup {[c EXCEPT
                                       !.status = "ready",
                                       !.dst = pid,
                                       !.data_dst = data_r]}
          (* Use c's existing communication id *)
          /\ memory' = [memory EXCEPT ![pid][comm_r] = c.id]
               
     
     (* No matching AsyncSend communication request exists. *)
     (* Create a AsyncReceive request and push it in the Communications. *)
     \/ /\ ~ \exists c \in mailbox(rdv): c.status = "send" 
        /\ LET comm ==  
                 [id |-> Cardinality(Communications)+1,
                  status |-> "receive", 
                  dst |-> pid, 
                  data_dst |-> data_r]
           IN
             /\ Communications' = Communications \cup {comm}
             /\ memory' = [memory EXCEPT ![pid][comm_r] = comm.id]           
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
  /\ UNCHANGED <<  waitingQueue,Requests>>

(* Wait for at least one communication from a given list to complete *)
(* pid: the process ID issuing the wait *)
(* comms: the list of addresses in the process's memory where the communication ids are stored *)
Wait(pid, comms) ==
  /\ pid \in Proc
  /\ pc[pid] \in WaitIns
  
  /\ \E comm_r \in comms, c \in Communications: c.id = memory[pid][comm_r] /\
     \/ /\ c.status = "ready"
        /\ memory' = [memory EXCEPT ![c.dst][c.data_dst] = memory[c.src][c.data_src]]
        /\ Communications' = (Communications \ {c}) \cup {[c EXCEPT !.status = "done"]}
     \/ /\ c.status = "done"
        /\ UNCHANGED <<memory,Communications, waitingQueue,Requests>>
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]

(* Test if at least one communication from a given list has completed *)
(* pid: the process ID issuing the wait *)
(* comms: the list of addresses in the process's memory where the communication ids are stored *)
(* ret_r: the address in the process's memory where the result is going to be stored *)
Test(pid, comms, ret_r) ==
  /\ ret_r \in Addr
  /\ pid \in Proc
  /\ pc[pid] \in TestIns
  /\ \/ \E comm_r \in comms, c\in Communications: c.id = memory[pid][comm_r] /\
        \/ /\ c.status = "ready"
           /\ memory' = [memory EXCEPT ![c.dst][c.data_dst] = memory[c.src][c.data_src],
                                        ![pid][ret_r] = ValTrue]
           /\ Communications' = (Communications \ {c}) \cup {[c EXCEPT !.status = "done"]}
        \/ /\ c.status = "done"
           /\ memory' = [memory EXCEPT ![pid][ret_r] = ValTrue]
           /\ UNCHANGED <<Communications,   waitingQueue>>
           
           
     \/ ~ \exists comm_r \in comms, c \in Communications: c.id = memory[pid][comm_r]
        /\ c.status \in {"ready","done"}
        /\ memory' = [memory EXCEPT ![pid][ret_r] = ValFalse]
        /\ UNCHANGED <<Communications,  waitingQueue,Requests>> 
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]

(* Local instruction execution *)
Local(pid) ==
    /\ pid \in Proc
    /\ pc[pid] \in LocalIns
   (* /\ memory' \in [Proc -> [Addr -> Nat]]
    /\ \forall p \in Proc, a \in Addr: memory'[p][a] /= memory[p][a]
       => p = pid /\ a \notin CommBuffers(pid) *)
    /\ memory'= [memory EXCEPT ![pid]  = [Addr -> Nat]]
    /\ \forall a \in Addr: memory'[pid][a] /= memory[pid][a]
       => a \notin CommBuffers(pid)
    /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
    /\ UNCHANGED <<Communications, waitingQueue,Requests>>
----------------------------------------------------------------------------------------------------------------

MutexAsyncLock(pid, mid) ==
   /\ pid \in Proc
   /\ pc[pid] \in LockIns
   /\ mid \in Mutex
   /\ \/ /\ ~isMember(pid, waitingQueue[mid]) 
         /\ Requests'  = [Requests EXCEPT ![pid]= Requests[pid] \cup {mid}]
         /\ waitingQueue' = [waitingQueue EXCEPT ![mid] = Append(waitingQueue[mid],pid)] 
      \/ /\ isMember(pid, waitingQueue[mid]) 
         /\ UNCHANGED <<memory, Communications, waitingQueue, Requests>>  
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]

(* When a process <pid> does a valid unlock() on Mutex <mid>, then:
 * - If <pid> is the owner (head of waitingQueue), that's a naive unlock and we 
 *     remove all linking between pid and mid that was created in ilock().
 * - If <pid> is not the owner, that's a cancel, and we remove the linking anyway.
 *
 * - If <pid> is not even in the waitingQueue (it did not ask for the <mid> previously),
 *   that's not enabled, and <pid> is blocked. Too bad for it.
 *)
MutexUnlock(pid, mid) ==
   /\ pid \in Proc
   /\ mid \in Mutex
   /\ pc[pid] \in UnlockIns
   
   (* If the request was previously posted (either owner or not) remove any linking *)
   /\ isMember(pid, waitingQueue[mid]) 
   /\ waitingQueue' = [waitingQueue EXCEPT ![mid] = Remove(pid,waitingQueue[mid])]
   /\ Requests' = [Requests EXCEPT ![pid] = Requests[pid] \ {mid}]
   (* If not a member, the transition is not enabled *)
   
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
   /\ UNCHANGED <<memory, Communications>>  

MutexWait(pid, mid) == 
/\ pid \in Proc
/\ mid \in Mutex
/\ pc[pid] \in MwaitIns
/\ isHead(pid, waitingQueue[mid]) (* transition enabled iff pid is owner *)
/\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
/\ UNCHANGED <<memory, Communications,waitingQueue, Requests>>
(* When a process <pid> does a mutex_wait on <mid>, 
 *  - If <pid> is the owner of <mid>, then proceed
 *  - If not, the transition is not enabled
 *)



----------------------------------------------------------------------------------------------------------------


(* Initially there are no messages in the Communications and the memory can have anything in their memories *)

Init == /\ Communications = {}
        /\ memory \in [Proc -> [Addr -> {0}]]
        /\ waitingQueue = [i \in Mutex |-> << >>]
        (*/\ pc = CHOOSE f : f \in [Proc -> Instr]*)
         /\ pc = CHOOSE f \in [Proc -> Instr] : TRUE
        
        

(*
Next == \exists p \in Proc, data_r \in Addr, comm_r \in Addr, rdv \in RdV,
                ret_r \in Addr, ids \in SUBSET Communications, mutex \in Mutex:
          \/ AsyncSend(p, rdv, data_r, comm_r)
          \/ AsyncReceive(p, rdv, data_r, comm_r)
          \/ Wait(p, comm_r)
          \/ Test(p, comm_r, ret_r)
          \/ Local(p)
          \/ Lock(p,mutex)
          \/ Unlock(p,mutex)
          \/ Mwait(p, mutex)
          \/ Mtest(p,mutex)          
 *)

Next == \exists p \in Proc, data_r \in Addr, comm_r \in Addr, rdv \in RdV,
                ret_r \in Addr, ids \in SUBSET Communications, mutex \in Mutex:
          \/ AsyncSend(p, rdv, data_r, comm_r)
          \/ AsyncReceive(p, rdv, data_r, comm_r)
          \/ Wait(p, comm_r)
          \/ Test(p, comm_r, ret_r)
          \/ Local(p)
         (* \/ Lock(p,mutex)
          \/ Unlock(p,mutex)
          \/ Mwait(p, mutex)
          \/ Mtest(p,mutex)   *)  
          
Spec == Init /\ [][Next]_<<pc, Communications,memory,waitingQueue >>
-----------------------------------------------------------------------------------------------------------------

------------------------------------------
(* Independence operator *)
I(A,B) == ENABLED A /\ ENABLED B => /\ A => (ENABLED B)'
                                    /\ B => (ENABLED A)'
                                    /\ A \cdot B \equiv B \cdot A
                                    
(* Independence of iAsyncSend / iAsyncReceive steps *)
THEOREM \forall p1, p2 \in Proc: \forall rdv1, rdv2 \in RdV: 
        \forall data1, data2, comm1, comm2 \in Addr:
        /\ p1 /= p2
        /\ ENABLED AsyncSend(p1, rdv1, data1, comm1)
        /\ ENABLED AsyncReceive(p2, rdv2, data2, comm2)
        => I(AsyncSend(p1, rdv1, data1, comm1), AsyncReceive(p2, rdv2, data2, comm2))

(* Independence of iAsyncSend and Wait *)
THEOREM \forall p1, p2 \in Proc: \forall data, comm1, comm2 \in Addr:
        \forall rdv \in RdV: \exists c \in Communications:
        /\ p1 /= p2
        /\ c.id = memory[p2][comm2]
        /\ \/ (p1 /= c.dst /\ p1 /= c.src)
           \/ (comm1 /= c.data_src /\ comm1 /= c.data_dst)
        /\ ENABLED AsyncSend(p1, rdv, data, comm1)
        /\ ENABLED Wait(p2, comm2)
        => I(AsyncSend(p1, rdv, data, comm1), Wait(p2, comm2)) 

(* Independence of iAsyncSend's in different rendez-vous *)
THEOREM \forall p1, p2 \in Proc: \forall rdv1, rdv2 \in RdV: 
        \forall data1, data2, comm1, comm2 \in Addr:
        /\ p1 /= p2
        /\ rdv1 /= rdv2
        /\ ENABLED AsyncSend(p1, rdv1, data1, comm1)
        /\ ENABLED AsyncSend(p2, rdv2, data2, comm2)
        => I(AsyncSend(p1, rdv1, data1, comm1),
             AsyncSend(p2, rdv2, data2, comm2))

(* Independence of iAsyncReceive's in different rendez-vous *)
THEOREM \forall p1, p2 \in Proc: \forall rdv1, rdv2 \in RdV: 
        \forall data1, data2, comm1, comm2 \in Addr:
        /\ p1 /= p2
        /\ rdv1 /= rdv2
        /\ ENABLED AsyncReceive(p1, rdv1, data1, comm1)
        /\ ENABLED AsyncReceive(p2, rdv2, data2, comm2)
        => I(AsyncReceive(p1, rdv1, data1, comm1),
             AsyncReceive(p2, rdv2, data2, comm2))

(* Independence of Wait of different processes on the same comm *)
THEOREM \forall p1, p2 \in Proc: \forall comm1, comm2 \in Addr:
        /\ p1 /= p2
        /\ comm1 = comm2
        /\ ENABLED Wait(p1, comm1)
        /\ ENABLED Wait(p2, comm2)
        => I(Wait(p1, comm1), Wait(p2, comm2))
====
\* Generated at Thu Feb 18 13:49:35 CET 2010


=============================================================================
\* Modification History
\* Last modified Thu May 03 10:20:11 CEST 2018 by diep-chi
\* Created Fri Jan 12 18:32:38 CET 2018 by diep-chi
