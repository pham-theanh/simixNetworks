--------------------------- MODULE simixNetworks ---------------------------
(* This is a TLA module specifying the networking layer of SIMIX. 
   It is used to verify the soundness of the DPOR reduction algorithm
   used in the model-checker. 

   If you think you found a new independence lemma, add it to this
   file and relaunch TLC to check whether your lemma actually holds.
   *)
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS RdV, Addr, Proc, Mutex, ValTrue, ValFalse, SendIns, RecvIns, WaitIns, 
          TestIns, LocalIns, LockIns, UnlockIns, MtestIns, MwaitIns
VARIABLES Communications, memory, testMemory, pc, pcState, waitedQueue

NoProc == CHOOSE p : p \notin Proc
NoAddr == CHOOSE a : a \notin Addr

Partition(S) == \forall x,y \in S : x \cap y /= {} => x = y
Instr ==UNION {SendIns, RecvIns, WaitIns, TestIns, LocalIns,LockIns, UnlockIns, MtestIns, MwaitIns}

Comm == [id:Nat,
         rdv:RdV,
         status:{"send","recv","ready","done"},
         src:Proc,
         dst:Proc,
         data_src:Addr,
         data_dst:Addr]


isHead(m,q) == IF q = <<>> THEN FALSE  
                ELSE IF m = Head(q) THEN  TRUE
                     ELSE FALSE 

isContain(q,m) == IF \E i \in (1..Len(q)): m = q[i] THEN TRUE
                    ELSE FALSE

ASSUME ValTrue \in Nat
ASSUME ValFalse \in Nat

(* The set of all the instructions *)
ASSUME Partition({SendIns, RecvIns, WaitIns, TestIns, LocalIns}) 


(* Let's keep everything in the right domains *)
TypeInv == /\ Communications \subseteq Comm
           /\ memory \in [Proc -> [Addr -> Nat]]
           /\ pc \in [Proc -> Instr]

(* The set of all communications waiting at rdv *)
(* ----- mailbox is updated automatically when updating the network ?? *)
mailbox(rdv) == {comm \in Communications : comm.rdv=rdv /\ comm.status \in {"send","recv"}}


(* The set of memory addresses of a process being used in a communication *)
CommBuffers(pid) == 
  {c.data_src: c \in { y \in Communications: y.status /= "done" /\ (y.src = pid \/ y.dst = pid)}} 
\cup {c.data_dst: c \in { y \in Communications: y.status /= "done" /\ (y.src = pid \/ y.dst = pid)}}

(* This is a send step of the system *)
(* pid: the process ID of the sender *)
(* rdv: the rendez-vous point where the "send" communication request is going to be pushed *)
(* data_r: the address in the sender's memory where the data is stored *)
(* comm_r: the address in the sender's memory where to store the communication id *)
Send(pid, rdv, data_r, comm_r) == 
  /\ rdv \in RdV
  /\ pid \in Proc
  /\ data_r \in Addr
  /\ comm_r \in Addr
  /\ pc[pid] \in SendIns
   
     (* A matching recv request exists in the rendez-vous *)
     (* Complete the sender fields and set the communication to the ready state *)
  /\ \/ \exists c \in mailbox(rdv):
          /\ c.status="recv"
          /\ \forall d \in mailbox(rdv): d.status="recv" => c.id <= d.id
          /\ Communications' = 
               (Communications \ {c}) \cup {[c EXCEPT
                                       !.status = "ready",
                                       !.src = pid,
                                       !.data_src = data_r]}
          (* Use c's existing communication id *)
          /\ memory' = [memory EXCEPT ![pid][comm_r] = c.id]
               
     
     (* No matching recv communication request exists. *)
     (* Create a send request and push it in the Communications. *)
     \/ /\ ~ \exists c \in mailbox(rdv): c.status = "recv" 
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
  /\ UNCHANGED <<testMemory, pcState, waitedQueue>>
(* This is a receive step of the system *)
(* pid: the process ID of the receiver *)
(* rdv: the Rendez-vous where the "receive" communication request is going to be pushed *)
(* data_r: the address in the receivers's memory where the data is going to be stored *)
(* comm_r: the address in the receivers's memory where to store the communication id *)
Recv(pid, rdv, data_r, comm_r) == 
  /\ rdv \in RdV
  /\ pid \in Proc
  /\ data_r \in Addr
  /\ comm_r \in Addr
  /\ pc[pid] \in RecvIns
  
     (* A matching send request exists in the rendez-vous *)
     (* Complete the receiver fields and set the communication to the ready state *)
  /\ \/ \exists c \in mailbox(rdv):
          /\ c.status="send"
          /\ \forall d \in mailbox(rdv): d.status="send" => c.id <= d.id
          /\ network' = 
               (network \ {c}) \cup {[c EXCEPT
                                       !.status = "ready",
                                       !.dst = pid,
                                       !.data_dst = data_r]}
          (* Use c's existing communication id *)
          /\ memory' = [memory EXCEPT ![pid][comm_r] = c.id]
               
     
     (* No matching send communication request exists. *)
     (* Create a recv request and push it in the network. *)
     \/ /\ ~ \exists c \in mailbox(rdv): c.status = "send" 
        /\ LET comm ==  
                 [id |-> Cardinality(network)+1,
                  status |-> "recv", 
                  dst |-> pid, 
                  data_dst |-> data_r]
           IN
             /\ network' = network \cup {comm}
             /\ memory' = [memory EXCEPT ![pid][comm_r] = comm.id]           
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
  /\ UNCHANGED <<testMemory, pcState, waitedQueue>>

(* Wait for at least one communication from a given list to complete *)
(* pid: the process ID issuing the wait *)
(* comms: the list of addresses in the process's memory where the communication ids are stored *)
Wait(pid, comms) ==
  /\ pid \in Proc
  /\ pc[pid] \in WaitIns
  
  /\ \E comm_r \in comms, c \in network: c.id = memory[pid][comm_r] /\
     \/ /\ c.status = "ready"
        /\ memory' = [memory EXCEPT ![c.dst][c.data_dst] = memory[c.src][c.data_src]]
        /\ network' = (network \ {c}) \cup {[c EXCEPT !.status = "done"]}
     \/ /\ c.status = "done"
        /\ UNCHANGED <<memory,network,testMemory, pcState, waitedQueue>>
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]

(* Test if at least one communication from a given list has completed *)
(* pid: the process ID issuing the wait *)
(* comms: the list of addresses in the process's memory where the communication ids are stored *)
(* ret_r: the address in the process's memory where the result is going to be stored *)
Test(pid, comms, ret_r) ==
  /\ ret_r \in Addr
  /\ pid \in Proc
  /\ pc[pid] \in TestIns
  /\ \/ \E comm_r \in comms, c\in network: c.id = memory[pid][comm_r] /\
        \/ /\ c.status = "ready"
           /\ memory' = [memory EXCEPT ![c.dst][c.data_dst] = memory[c.src][c.data_src],
                                        ![pid][ret_r] = ValTrue]
           /\ network' = (network \ {c}) \cup {[c EXCEPT !.status = "done"]}
        \/ /\ c.status = "done"
           /\ memory' = [memory EXCEPT ![pid][ret_r] = ValTrue]
           /\ UNCHANGED <<network, testMemory, pcState, waitedQueue>>
           
           
     \/ ~ \exists comm_r \in comms, c \in network: c.id = memory[pid][comm_r]
        /\ c.status \in {"ready","done"}
        /\ memory' = [memory EXCEPT ![pid][ret_r] = ValFalse]
        /\ UNCHANGED <<network, testMemory, pcState, waitedQueue>> 
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
    /\ UNCHANGED <<network, testMemory, pcState, waitedQueue>>
----------------------------------------------------------------------------------------------------------------

Lock(pid,mid) ==
   /\ pid \in Proc
   /\ pc[pid] \in LockIns
   /\ mid \in Mutex
   /\ ~isContain(waitedQueue[mid],pid)
   /\ pcState[pid] /= "blocked"   
   /\ \/ /\ Len(waitedQueue[mid]) > 0 (*if the mutex is busy then block the process*)
         /\ pcState' = [pcState EXCEPT ![pid] = "blocked"]
         /\ UNCHANGED <<memory,network, testMemory >>
         
      \/ /\ Len(waitedQueue[mid])=0 
         /\ UNCHANGED <<memory,network, pcState,testMemory >>     
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
   /\ waitedQueue' = [waitedQueue EXCEPT ![mid] = Append(waitedQueue[mid],pid)]  
   
(*change unlock kill occuppied mutex, check unlock if pid = head(waitQueue)*)

Unlock(pid, mid) ==
   /\ pid \in Proc
   /\ pc[pid] \in UnlockIns
   /\ isHead(pid,waitedQueue[mid])
   /\ waitedQueue' = [waitedQueue EXCEPT ![mid] = Tail(waitedQueue[mid])] 
   /\ \/ /\  Len(waitedQueue[mid]) > 1       (* there is someone to wake up *)
         /\  LET e == Head(Tail(waitedQueue[mid]))         (*get the second process in the queue to wake it up*)
             IN pcState' = [pcState EXCEPT ![e] = "running"]
         /\ UNCHANGED <<memory,network,testMemory>>
               
      \/ /\ Len(waitedQueue[mid]) = 1
         /\ UNCHANGED <<memory,network,pcState,testMemory>>
   
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
   

(*
Mtest(pid, mid) ==
     /\ pid \in Proc
     /\ mid \in Mutex
     /\ pc[pid] \in MtestIns
     /\ \/ /\ \/ Len(waitedQueue[mid]) =0
              \/ isHead(pid,waitedQueue[mid])
           /\ testMemory' = [testMemory EXCEPT ![pid][mid] = ValTrue]
        \/ /\ \/ Len(waitedQueue[mid]) > 0 
              \/ ~isHead(pid,waitedQueue[mid])
           /\ testMemory' = [testMemory EXCEPT ![pid][mid] = ValFalse]
      
     /\ UNCHANGED <<memory,network, pcState,waitedQueue,occupiedMutex >>
     /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
  

Mwait(pid, mid) ==
     /\ pid \in Proc
     /\ mid \in Mutex
     /\ pc[pid] \in MwaitIns
     /\  \/ Len(waitedQueue[mid]) =0
         \/ isHead(pid,waitedQueue[mid])
     /\ UNCHANGED <<memory,network, pcState,waitedQueue,occupiedMutex,testMemory >>
     /\ \E ins \in Instr : pc' = [pc EXCEPT ![pid] = ins]
     
*)


----------------------------------------------------------------------------------------------------------------


(* Initially there are no messages in the network and the memory can have anything in their memories *)

Init == /\ network = {}
        /\ memory \in [Proc -> [Addr -> {0}]]
        /\ testMemory \in [Proc -> [Mutex -> {0}]]
        /\ waitedQueue = [i \in Mutex |-> << >>]
        /\ pcState = [i \in Proc |-> "running"]
        (*/\ pc = CHOOSE f : f \in [Proc -> Instr]*)
         /\ pc = CHOOSE f \in [Proc -> Instr] : TRUE
        
        

(*
Next == \exists p \in Proc, data_r \in Addr, comm_r \in Addr, rdv \in RdV,
                ret_r \in Addr, ids \in SUBSET network, mutex \in Mutex:
          \/ Send(p, rdv, data_r, comm_r)
          \/ Recv(p, rdv, data_r, comm_r)
          \/ Wait(p, comm_r)
          \/ Test(p, comm_r, ret_r)
          \/ Local(p)
          \/ Lock(p,mutex)
          \/ Unlock(p,mutex)
          \/ Mwait(p, mutex)
          \/ Mtest(p,mutex)          
 *)

Next == \exists p \in Proc, data_r \in Addr, comm_r \in Addr, rdv \in RdV,
                ret_r \in Addr, ids \in SUBSET network, mutex \in Mutex:
          \/ Send(p, rdv, data_r, comm_r)
          \/ Recv(p, rdv, data_r, comm_r)
          \/ Wait(p, comm_r)
          \/ Test(p, comm_r, ret_r)
          \/ Local(p)
          \/ Lock(p,mutex)
          \/ Unlock(p,mutex)
         (* \/ Mwait(p, mutex)
          \/ Mtest(p,mutex)   *)  
          
Spec == Init /\ [][Next]_<<pc, network,memory,pcState,waitedQueue,testMemory >>
-----------------------------------------------------------------------------------------------------------------

------------------------------------------
(* Independence operator *)
I(A,B) == ENABLED A /\ ENABLED B => /\ A => (ENABLED B)'
                                    /\ B => (ENABLED A)'
                                    /\ A \cdot B \equiv B \cdot A
                                    
(* Independence of iSend / iRecv steps *)
THEOREM \forall p1, p2 \in Proc: \forall rdv1, rdv2 \in RdV: 
        \forall data1, data2, comm1, comm2 \in Addr:
        /\ p1 /= p2
        /\ ENABLED Send(p1, rdv1, data1, comm1)
        /\ ENABLED Recv(p2, rdv2, data2, comm2)
        => I(Send(p1, rdv1, data1, comm1), Recv(p2, rdv2, data2, comm2))

(* Independence of iSend and Wait *)
THEOREM \forall p1, p2 \in Proc: \forall data, comm1, comm2 \in Addr:
        \forall rdv \in RdV: \exists c \in network:
        /\ p1 /= p2
        /\ c.id = memory[p2][comm2]
        /\ \/ (p1 /= c.dst /\ p1 /= c.src)
           \/ (comm1 /= c.data_src /\ comm1 /= c.data_dst)
        /\ ENABLED Send(p1, rdv, data, comm1)
        /\ ENABLED Wait(p2, comm2)
        => I(Send(p1, rdv, data, comm1), Wait(p2, comm2)) 

(* Independence of iSend's in different rendez-vous *)
THEOREM \forall p1, p2 \in Proc: \forall rdv1, rdv2 \in RdV: 
        \forall data1, data2, comm1, comm2 \in Addr:
        /\ p1 /= p2
        /\ rdv1 /= rdv2
        /\ ENABLED Send(p1, rdv1, data1, comm1)
        /\ ENABLED Send(p2, rdv2, data2, comm2)
        => I(Send(p1, rdv1, data1, comm1),
             Send(p2, rdv2, data2, comm2))

(* Independence of iRecv's in different rendez-vous *)
THEOREM \forall p1, p2 \in Proc: \forall rdv1, rdv2 \in RdV: 
        \forall data1, data2, comm1, comm2 \in Addr:
        /\ p1 /= p2
        /\ rdv1 /= rdv2
        /\ ENABLED Recv(p1, rdv1, data1, comm1)
        /\ ENABLED Recv(p2, rdv2, data2, comm2)
        => I(Recv(p1, rdv1, data1, comm1),
             Recv(p2, rdv2, data2, comm2))

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
\* Last modified Thu Jan 11 14:28:52 CET 2018 by diep-chi
\* Created Mon Nov 27 17:50:43 CET 2017 by diep-chi
